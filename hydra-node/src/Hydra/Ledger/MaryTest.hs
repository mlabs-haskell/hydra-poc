{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | A simplified "Mary" ledger, which is initialized with a genesis UTXO set
-- and also some example transactions. Use this with 'cardanoLedger'.
module Hydra.Ledger.MaryTest where

import Cardano.Prelude

-- REVIEW(SN): use a more consistent set of ledger imports, but some things not
-- in the API?

import Cardano.Binary (DecoderError, decodeAnnotator, fromCBOR, serialize)
import Cardano.Ledger.SafeHash (hashAnnotated)
import Cardano.Ledger.ShelleyMA.Timelocks (ValidityInterval (..))
import Cardano.Ledger.ShelleyMA.TxBody (TxBody (TxBody))
import Cardano.Ledger.Val ((<->))
import qualified Cardano.Ledger.Val as Val
import Cardano.Slotting.EpochInfo (fixedSizeEpochInfo)
import Cardano.Slotting.Slot (EpochSize (EpochSize))
import Data.Default (def)
import qualified Data.Map as Map
import qualified Data.Sequence.Strict as StrictSeq
import qualified Data.Set as Set
import Hydra.Ledger (Ledger (..), Tx (..), ValidationError (..), ValidationResult (..))
import Shelley.Spec.Ledger.API (
  Addr,
  Coin (..),
  Globals (..),
  KeyPair,
  KeyRole (Payment, Staking),
  Network (Testnet),
  StrictMaybe (SNothing),
  TxId,
  TxIn (TxIn),
  TxOut (..),
  Wdrl (..),
 )
import qualified Shelley.Spec.Ledger.API as Ledger
import qualified Shelley.Spec.Ledger.API as Ledgers hiding (Tx)
import Shelley.Spec.Ledger.BaseTypes (UnitInterval, mkActiveSlotCoeff, mkUnitInterval)
import Shelley.Spec.Ledger.Keys (KeyPair (KeyPair), asWitness)
import Shelley.Spec.Ledger.LedgerState (LedgerState (..), UTxOState (..))
import Shelley.Spec.Ledger.PParams (emptyPParams)
import Shelley.Spec.Ledger.Slot (SlotNo (SlotNo))
import Shelley.Spec.Ledger.Tx (addrWits)
import Shelley.Spec.Ledger.UTxO (UTxO (..), makeWitnessesVKey, txid)
import Test.Cardano.Ledger.EraBuffet (MaryEra, TestCrypto, Value)
import Test.Shelley.Spec.Ledger.Utils (mkAddr, mkKeyPair)

type MaryTest = MaryEra TestCrypto

mkLedgerEnv :: Ledgers.LedgersEnv MaryTest
mkLedgerEnv =
  Ledgers.LedgersEnv
    { Ledgers.ledgersSlotNo = SlotNo 1
    , Ledgers.ledgersPp = emptyPParams
    , Ledgers.ledgersAccount = panic "Not implemented"
    }

mkLedgerState :: Ledger.LedgerState MaryTest
mkLedgerState =
  def{_utxoState = def{_utxo = initUTxO}}

type MaryTestTx = Ledger.Tx MaryTest

decodeTx :: LByteString -> Either DecoderError MaryTestTx
decodeTx = decodeAnnotator "tx" fromCBOR

encodeTx :: MaryTestTx -> LByteString
encodeTx = serialize

-- * Cardano ledger

instance Tx MaryTestTx where
  type UTxO MaryTestTx = Ledger.UTxO MaryTest
  type LedgerState MaryTestTx = Ledger.LedgerState MaryTest

cardanoLedger ::
  Ledger.LedgersEnv MaryTest ->
  Ledger (Ledger.Tx MaryTest)
cardanoLedger env =
  Ledger
    { canApply = validateTx env
    , applyTransaction = applyTx env
    , initLedgerState = def
    , getUTxO = Ledger._utxo . Ledger._utxoState
    }

applyTx ::
  Ledger.LedgersEnv MaryTest ->
  Ledger.LedgerState MaryTest ->
  Ledger.Tx MaryTest ->
  Either ValidationError (Ledger.LedgerState MaryTest)
applyTx env ls tx =
  first toValidationError $ Ledger.applyTxsTransition globals env (pure tx) ls
 where
  -- toValidationError :: ApplyTxError -> ValidationError
  toValidationError = const ValidationError

validateTx ::
  Ledger.LedgersEnv MaryTest ->
  Ledger.LedgerState MaryTest ->
  Ledger.Tx MaryTest ->
  ValidationResult
validateTx env ls tx =
  either (Invalid . toValidationError) (const Valid) $
    Ledger.applyTxsTransition globals env (pure tx) ls
 where
  -- toValidationError :: ApplyTxError -> ValidationError
  toValidationError = const ValidationError

--
-- From: shelley/chain-and-ledger/shelley-spec-ledger-test/src/Test/Shelley/Spec/Ledger/Utils.hs
--

-- TODO(SN): not hard-code these obviously
globals :: Globals
globals =
  Globals
    { epochInfo = fixedSizeEpochInfo $ EpochSize 100
    , slotsPerKESPeriod = 20
    , stabilityWindow = 33
    , randomnessStabilisationWindow = 33
    , securityParameter = 10
    , maxKESEvo = 10
    , quorum = 5
    , maxMajorPV = 1000
    , maxLovelaceSupply = 45 * 1000 * 1000 * 1000 * 1000 * 1000
    , activeSlotCoeff = mkActiveSlotCoeff . unsafeMkUnitInterval $ 0.9
    , networkId = Testnet
    }

-- | You vouch that argument is in [0; 1].
unsafeMkUnitInterval :: Ratio Word64 -> UnitInterval
unsafeMkUnitInterval r =
  fromMaybe (panic "could not construct unit interval") $ mkUnitInterval r

--
-- From: shelley-ma/shelley-ma-test/test/Test/Cardano/Ledger/Mary/Examples/MultiAssets.hs
--

aliceInitCoin :: Coin
aliceInitCoin = Coin $ 10 * 1000 * 1000 * 1000 * 1000 * 1000

bobInitCoin :: Coin
bobInitCoin = Coin $ 1 * 1000 * 1000 * 1000 * 1000 * 1000

unboundedInterval :: ValidityInterval
unboundedInterval = ValidityInterval SNothing SNothing

bootstrapTxId :: TxId TestCrypto
bootstrapTxId = txid @MaryTest txb
 where
  txb :: TxBody MaryTest
  txb =
    TxBody
      Set.empty
      StrictSeq.empty
      StrictSeq.empty
      (Wdrl Map.empty)
      (Coin 0)
      unboundedInterval
      SNothing
      SNothing
      (Val.inject (Coin 0))

initUTxO :: Ledger.UTxO MaryTest
initUTxO =
  UTxO $
    Map.fromList
      [ (TxIn bootstrapTxId 0, TxOut aliceAddr (Val.inject aliceInitCoin))
      , (TxIn bootstrapTxId 1, TxOut bobAddr (Val.inject bobInitCoin))
      ]

-- | Alice's payment key pair
alicePay :: KeyPair 'Payment TestCrypto
alicePay = KeyPair vk sk
 where
  (sk, vk) = mkKeyPair (0, 0, 0, 0, 0)

-- | Alice's stake key pair
aliceStake :: KeyPair 'Staking TestCrypto
aliceStake = KeyPair vk sk
 where
  (sk, vk) = mkKeyPair (1, 1, 1, 1, 1)

-- | Alice's base address
aliceAddr :: Addr TestCrypto
aliceAddr = mkAddr (alicePay, aliceStake)

-- | Bob's payment key pair
bobPay :: KeyPair 'Payment TestCrypto
bobPay = KeyPair vk sk
 where
  (sk, vk) = mkKeyPair (2, 2, 2, 2, 2)

-- | Bob's stake key pair
bobStake :: KeyPair 'Staking TestCrypto
bobStake = KeyPair vk sk
 where
  (sk, vk) = mkKeyPair (3, 3, 3, 3, 3)

-- | Bob's address
bobAddr :: Addr TestCrypto
bobAddr = mkAddr (bobPay, bobStake)

--
-- From: shelley-ma/shelley-ma-test/test/Test/Cardano/Ledger/Mary/Examples/Cast.hs
--

-- These examples do not use several of the transaction components,
-- so we can simplify building them.
makeTxb ::
  [TxIn TestCrypto] ->
  [TxOut MaryTest] ->
  ValidityInterval ->
  Value MaryTest ->
  TxBody MaryTest
makeTxb ins outs interval =
  TxBody
    (Set.fromList ins)
    (StrictSeq.fromList outs)
    StrictSeq.empty
    (Wdrl Map.empty)
    feeEx
    interval
    SNothing
    SNothing

feeEx :: Coin
feeEx = Coin 3

--
-- Example transactions
--

-- | Some invalid tx (unbalanced and no witnesses).
txInvalid :: Ledger.Tx MaryTest
txInvalid = Ledger.Tx (makeTxb [TxIn bootstrapTxId 0] [] unboundedInterval Val.zero) mempty SNothing

-- | Alice gives five Ada to Bob.
txSimpleTransfer :: Ledger.Tx MaryTest
txSimpleTransfer =
  Ledger.Tx
    txbody
    mempty{addrWits = makeWitnessesVKey (hashAnnotated txbody) [asWitness alicePay]}
    SNothing
 where
  txbody :: TxBody MaryTest
  txbody =
    makeTxb
      [TxIn bootstrapTxId 0]
      [ TxOut aliceAddr $ Val.inject $ aliceInitCoin <-> feeEx <-> transfered -- TODO(SN): remove fee?
      , TxOut bobAddr $ Val.inject transfered
      ]
      unboundedInterval
      Val.zero

  transfered = Coin 5
