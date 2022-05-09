{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-specialize #-}

module Hydra.Contract.Head where

import PlutusTx.Prelude

import Hydra.Contract.Commit (SerializedTxOut (..))
import qualified Hydra.Contract.Commit as Commit
import Hydra.Contract.HeadState (Input (..), Signature, SnapshotNumber, State (..))
import qualified Hydra.Contract.Initial as Initial
import Hydra.Data.ContestationPeriod (ContestationPeriod)
import Hydra.Data.Party (Party (vkey))
import Plutus.Extras (ValidatorType, scriptValidatorHash, wrapValidator)
import Plutus.V2.Ledger.Api (
  Address,
  CurrencySymbol,
  Datum (..),
  FromData (fromBuiltinData),
  OutputDatum (..),
  PubKeyHash (getPubKeyHash),
  Script,
  ScriptContext (..),
  ToData (toBuiltinData),
  TokenName (..),
  TxInInfo (..),
  TxInfo (..),
  TxOut (..),
  Validator (getValidator),
  ValidatorHash,
  Value (Value),
  adaSymbol,
  adaToken,
  mkValidatorScript,
 )
import Plutus.V2.Ledger.Contexts (findDatum, findOwnInput)
import PlutusTx (CompiledCode)
import qualified PlutusTx
import qualified PlutusTx.AssocMap as Map
import qualified PlutusTx.Builtins as Builtins

-- NOTE: Functions not re-exported "as V2", but using the same data types.
import Plutus.V1.Ledger.Address (scriptHashAddress)
import Plutus.V1.Ledger.Value (assetClass, assetClassValue, valueOf)

type DatumType = State
type RedeemerType = Input

hydraHeadV1 :: BuiltinByteString
hydraHeadV1 = "HydraHeadV1"

{-# INLINEABLE headValidator #-}
headValidator ::
  -- | Commit script address. NOTE: Used to identify inputs from commits and
  -- likely could be replaced by looking for PTs.
  Address ->
  -- | Inital script address. NOTE: Used to identify inputs from initials and
  -- likely could be replaced by looking for PTs.
  Address ->
  State ->
  Input ->
  ScriptContext ->
  Bool
headValidator commitAddress initialAddress oldState input context =
  case (oldState, input) of
    (Initial{contestationPeriod, parties}, CollectCom) ->
      checkCollectCom context headContext (contestationPeriod, parties)
    (Initial{parties}, Abort) ->
      checkAbort context headContext parties
    (Open{parties}, Close{snapshotNumber, signature}) ->
      checkClose context headContext parties snapshotNumber signature
    (Closed{utxoHash}, Fanout{numberOfFanoutOutputs}) ->
      checkFanout utxoHash numberOfFanoutOutputs context
    _ -> traceError "invalid head state transition"
 where
  headContext = mkHeadContext context initialAddress commitAddress

data CheckCollectComError
  = NoContinuingOutput
  | MoreThanOneContinuingOutput
  | OutputValueNotPreserved
  | OutputHashNotMatching

data HeadContext = HeadContext
  { headAddress :: Address
  , headInputValue :: Value
  , headCurrencySymbol :: CurrencySymbol
  , commitAddress :: Address
  , initialAddress :: Address
  }

mkHeadContext :: ScriptContext -> Address -> Address -> HeadContext
mkHeadContext context initialAddress commitAddress =
  HeadContext
    { headAddress
    , headInputValue
    , headCurrencySymbol
    , initialAddress
    , commitAddress
    }
 where
  headInput :: TxInInfo
  headInput =
    fromMaybe
      (traceError "script not spending a head input?")
      (findOwnInput context)

  headInputValue :: Value
  headInputValue =
    txOutValue (txInInfoResolved headInput)

  headAddress :: Address
  headAddress =
    txOutAddress (txInInfoResolved headInput)

  headCurrencySymbol :: CurrencySymbol
  headCurrencySymbol =
    headInputValue
      & findCandidateSymbols
      & \case
        [s] -> s
        _ -> traceError "malformed thread token, expected exactly one asset."

  findCandidateSymbols :: Value -> [CurrencySymbol]
  findCandidateSymbols (Value v) = loop (Map.toList v)
   where
    loop = \case
      [] -> []
      (symbol, assets) : rest ->
        case filter ((TokenName hydraHeadV1, 1) ==) (Map.toList assets) of
          [] -> loop rest
          _ -> symbol : loop rest
{-# INLINEABLE mkHeadContext #-}

-- | On-Chain Validation for 'Abort' transition.
-- It must verify that:
--  * All PTs have been burnt
--  * It has collected inputs for all parties, either from `Initial` or `Commit` script.
checkAbort ::
  ScriptContext ->
  HeadContext ->
  [Party] ->
  Bool
checkAbort context@ScriptContext{scriptContextTxInfo = txInfo} headContext parties =
  consumeInputsForAllParties
    && mustBeSignedByParticipant context headContext
 where
  HeadContext{initialAddress, commitAddress} = headContext

  consumeInputsForAllParties =
    traceIfFalse "number of inputs do not match number of parties" $
      length parties == length initialAndCommitInputs
  initialAndCommitInputs =
    filter
      ( \TxInInfo{txInInfoResolved} ->
          let addr = txOutAddress txInInfoResolved
           in addr == commitAddress || addr == initialAddress
      )
      (txInfoInputs txInfo)

-- | On-Chain Validation for the 'CollectCom' transition.
--
-- The 'CollectCom' transition must verify that:
--
-- - All participants have committed (even empty commits)
-- - All commits are properly collected and locked into the contract
-- - The transaction is performed (i.e. signed) by one of the head participants
--
-- It must also Initialize the on-chain state η* with a snapshot number and a
-- Merkle-Tree root hash of committed outputs.
--
-- (*) In principle, η contains not a hash but a full UTXO set as well as a set
-- of dangling transactions. However, in the coordinated version of the
-- protocol, there can't be any dangling transactions and thus, it is no longer
-- required to check applicability of those transactions to the UTXO set. It
-- suffices to store a hash of the resulting outputs of that UTXO instead.
checkCollectCom ::
  -- | Script execution context
  ScriptContext ->
  -- | Static information about the head (i.e. address, value, currency...)
  HeadContext ->
  -- | Initial state
  (ContestationPeriod, [Party]) ->
  Bool
checkCollectCom context@ScriptContext{scriptContextTxInfo = txInfo} headContext (_, parties) =
  mustContinueHeadWith context headAddress expectedChangeValue expectedOutputDatum
    && everyoneHasCommitted
    && mustBeSignedByParticipant context headContext
 where
  everyoneHasCommitted =
    traceIfFalse "not everyone committed" $
      nTotalCommits == length parties

  HeadContext
    { headAddress
    , headCurrencySymbol
    , commitAddress
    } = headContext

  (expectedChangeValue, collectedCommits, nTotalCommits) =
    traverseInputs
      (negate (txInfoAdaFee txInfo), [], 0)
      (txInfoInputs txInfo)

  expectedOutputDatum :: Datum
  expectedOutputDatum =
    let utxoHash = Builtins.serialiseData $ toBuiltinData collectedCommits
     in Datum $ toBuiltinData Open{parties, utxoHash}

  traverseInputs (fuel, commits, nCommits) = \case
    [] ->
      (fuel, commits, nCommits)
    TxInInfo{txInInfoResolved} : rest
      | txOutAddress txInInfoResolved == headAddress ->
        traverseInputs
          (fuel, commits, nCommits)
          rest
      | txOutAddress txInInfoResolved == commitAddress ->
        case commitFrom txInInfoResolved of
          (commitValue, Just (SerializedTxOut commit)) ->
            case matchParticipationToken headCurrencySymbol commitValue of
              [_] ->
                traverseInputs
                  (fuel, commits <> [commit], succ nCommits)
                  rest
              _ ->
                traceError "Invalid commit: does not contain valid PT."
          (commitValue, Nothing) ->
            case matchParticipationToken headCurrencySymbol commitValue of
              [_] ->
                traverseInputs
                  (fuel, commits, succ nCommits)
                  rest
              _ ->
                traceError "Invalid commit: does not contain valid PT."
      | otherwise ->
        traverseInputs
          (fuel + txOutAdaValue txInInfoResolved, commits, nCommits)
          rest

  commitFrom :: TxOut -> (Value, Maybe SerializedTxOut)
  commitFrom o = do
    let d = findTxOutDatum txInfo o
    case fromBuiltinData @Commit.DatumType $ getDatum d of
      Just (_p, _, Just serializedTxOut) ->
        (txOutValue o, Just serializedTxOut)
      Just (_p, _, Nothing) ->
        (txOutValue o, Nothing)
      Nothing ->
        traceError "commitFrom failed fromBuiltinData"
{-# INLINEABLE checkCollectCom #-}

checkClose ::
  ScriptContext ->
  HeadContext ->
  [Party] ->
  SnapshotNumber ->
  [Signature] ->
  Bool
checkClose context headContext parties snapshotNumber sig =
  checkSnapshot && mustBeSignedByParticipant context headContext
 where
  checkSnapshot
    | snapshotNumber == 0 = True
    | snapshotNumber > 0 = verifySnapshotSignature parties snapshotNumber sig
    | otherwise = traceError "negative snapshot number"
{-# INLINEABLE checkClose #-}

txOutAdaValue :: TxOut -> Integer
txOutAdaValue o = valueOf (txOutValue o) adaSymbol adaToken
{-# INLINEABLE txOutAdaValue #-}

txInfoAdaFee :: TxInfo -> Integer
txInfoAdaFee tx = valueOf (txInfoFee tx) adaSymbol adaToken
{-# INLINEABLE txInfoAdaFee #-}

checkFanout ::
  BuiltinByteString ->
  Integer ->
  ScriptContext ->
  Bool
checkFanout utxoHash numberOfFanoutOutputs ScriptContext{scriptContextTxInfo = txInfo} =
  traceIfFalse "fannedOutUtxoHash /= closedUtxoHash" $ fannedOutUtxoHash == utxoHash
 where
  fannedOutUtxoHash = hashTxOuts $ take numberOfFanoutOutputs txInfoOutputs
  TxInfo{txInfoOutputs} = txInfo
{-# INLINEABLE checkFanout #-}

(&) :: a -> (a -> b) -> b
(&) = flip ($)
{-# INLINEABLE (&) #-}

mustBeSignedByParticipant ::
  ScriptContext ->
  HeadContext ->
  Bool
mustBeSignedByParticipant ScriptContext{scriptContextTxInfo = txInfo} HeadContext{headCurrencySymbol} =
  case getPubKeyHash <$> txInfoSignatories txInfo of
    [signer] ->
      traceIfFalse "mustBeSignedByParticipant: did not find expected signer" $
        signer `elem` (unTokenName <$> participationTokens)
    [] ->
      traceError "mustBeSignedByParticipant: no signers"
    _ ->
      traceError "mustBeSignedByParticipant: too many signers"
 where
  participationTokens = loop (txInfoInputs txInfo)
  loop = \case
    [] -> []
    (TxInInfo{txInInfoResolved} : rest) ->
      matchParticipationToken headCurrencySymbol (txOutValue txInInfoResolved) ++ loop rest
{-# INLINEABLE mustBeSignedByParticipant #-}

matchParticipationToken :: CurrencySymbol -> Value -> [TokenName]
matchParticipationToken headCurrency (Value val) =
  case Map.toList <$> Map.lookup headCurrency val of
    Just tokens ->
      mapMaybe (\(tokenName, n) -> if n == 1 then Just tokenName else Nothing) tokens
    _ ->
      []
{-# INLINEABLE matchParticipationToken #-}

mustContinueHeadWith :: ScriptContext -> Address -> Integer -> Datum -> Bool
mustContinueHeadWith ScriptContext{scriptContextTxInfo = txInfo} headAddress changeValue datum =
  checkOutputDatum [] (txInfoOutputs txInfo)
 where
  checkOutputDatum xs = \case
    [] ->
      traceError "no continuing head output"
    (o : rest)
      | txOutAddress o == headAddress ->
        traceIfFalse "wrong output head datum" (findTxOutDatum txInfo o == datum)
          && traceIfFalse "wrong output value" (checkOutputValue (xs <> rest))
    (o : rest) ->
      checkOutputDatum (o : xs) rest

  checkOutputValue = \case
    [] ->
      True
    [o]
      | txOutAddress o /= headAddress ->
        txOutValue o == lovelaceValue changeValue
    _ ->
      traceError "invalid collect-com outputs: more than 2 outputs."

  lovelaceValue = assetClassValue (assetClass adaSymbol adaToken)
{-# INLINEABLE mustContinueHeadWith #-}

findTxOutDatum :: TxInfo -> TxOut -> Datum
findTxOutDatum txInfo o =
  case txOutDatum o of
    NoOutputDatum -> traceError "no output datum"
    OutputDatumHash dh -> fromMaybe (traceError "datum not found") $ findDatum dh txInfo
    OutputDatum d -> d
{-# INLINEABLE findTxOutDatum #-}

hashPreSerializedCommits :: [SerializedTxOut] -> BuiltinByteString
hashPreSerializedCommits =
  -- REVIEW: Ensure BuiltinData 'List [Data]' is encoded like we expect
  sha2_256 . Builtins.serialiseData . toBuiltinData
{-# INLINEABLE hashPreSerializedCommits #-}

hashTxOuts :: [TxOut] -> BuiltinByteString
hashTxOuts =
  sha2_256 . Builtins.serialiseData . toBuiltinData
{-# INLINEABLE hashTxOuts #-}

verifySnapshotSignature :: [Party] -> SnapshotNumber -> [Signature] -> Bool
verifySnapshotSignature parties snapshotNumber sigs =
  traceIfFalse "signature verification failed" $
    length parties == length sigs
      && all (uncurry $ verifyPartySignature snapshotNumber) (zip parties sigs)
{-# INLINEABLE verifySnapshotSignature #-}

verifyPartySignature :: SnapshotNumber -> Party -> Signature -> Bool
verifyPartySignature snapshotNumber party signed =
  traceIfFalse "party signature verification failed" $
    verifySignature (vkey party) message signed
 where
  message = Builtins.serialiseData $ toBuiltinData snapshotNumber
{-# INLINEABLE verifyPartySignature #-}

-- TODO: Add a NetworkId so that we can properly serialise address hashes
-- see 'encodeAddress' for details
-- TODO: Use validatorHash directly in headValidator arguments
compiledValidator :: CompiledCode ValidatorType
compiledValidator =
  $$(PlutusTx.compile [||\ca ia -> wrap (headValidator ca ia)||])
    `PlutusTx.applyCode` PlutusTx.liftCode (scriptHashAddress Commit.validatorHash)
    `PlutusTx.applyCode` PlutusTx.liftCode (scriptHashAddress Initial.validatorHash)
 where
  wrap = wrapValidator @DatumType @RedeemerType

validatorScript :: Script
validatorScript = getValidator $ mkValidatorScript compiledValidator

validatorHash :: ValidatorHash
validatorHash = scriptValidatorHash validatorScript
