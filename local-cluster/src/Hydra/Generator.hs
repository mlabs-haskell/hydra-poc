{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeApplications #-}

module Hydra.Generator where

import Hydra.Prelude hiding (size)

import Cardano.Api
import Control.Monad (foldM)
import Data.Aeson (object, withObject, (.:), (.=))
import Hydra.Ledger (IsTx (..))
import Hydra.Ledger.Cardano (
  CardanoTx,
  Utxo,
  genFixedSizeSequenceOfValidTransactions,
  genKeyPair,
  genOneUtxoFor,
  genUtxoFor,
  mkSimpleCardanoTx,
  mkVkAddress,
  utxoFromTx,
  utxoPairs,
 )
import Test.QuickCheck (elements, generate, sized)

networkId :: NetworkId
networkId = Testnet $ NetworkMagic 42

-- | A 'Dataset' that can be run for testing purpose.
-- The 'transactionSequence' is guaranteed to be applicable, in sequence, to the 'initialUtxo'
-- set.
data Dataset = Dataset
  { initialUtxo :: Utxo
  , transactionsSequence :: [CardanoTx]
  , signingKey :: SigningKey PaymentKey
  }
  deriving (Show, Generic)

instance Arbitrary Dataset where
  arbitrary = sized genConstantUtxoDataset

instance ToJSON Dataset where
  toJSON Dataset{initialUtxo, transactionsSequence, signingKey} =
    object
      [ "initialUtxo" .= initialUtxo
      , "transactionsSequence" .= transactionsSequence
      , "signingKey" .= serialiseToBech32 signingKey
      ]

instance FromJSON Dataset where
  parseJSON =
    withObject "Dataset" $ \o ->
      Dataset <$> o .: "initialUtxo"
        <*> o .: "transactionsSequence"
        <*> (decodeSigningKey =<< o .: "signingKey")
   where
    decodeSigningKey =
      either (fail . show) pure . deserialiseFromBech32 (AsSigningKey AsPaymentKey)

-- | Generate an arbitrary UTXO set and a sequence of transactions for this set.
generateDataset :: Int -> IO Dataset
generateDataset = generate . genDataset

genDataset :: Int -> Gen Dataset
genDataset sequenceLength = do
  (verificationKey, signingKey) <- genKeyPair
  initialUtxo <- genUtxoFor verificationKey
  transactionsSequence <- genFixedSizeSequenceOfValidTransactions sequenceLength initialUtxo
  pure Dataset{initialUtxo, transactionsSequence, signingKey}

-- | Generate a 'Dataset' which does not grow the UTXO set over time.
generateConstantUtxoDataset :: Int -> IO Dataset
generateConstantUtxoDataset = generate . genConstantUtxoDataset

genConstantUtxoDataset :: Int -> Gen Dataset
genConstantUtxoDataset len = do
  keyPair@(verificationKey, signingKey) <- genKeyPair
  initialUtxo <- genOneUtxoFor verificationKey
  transactionsSequence <- reverse . thrd <$> foldM generateOneTransfer (initialUtxo, keyPair, []) [1 .. len]
  pure Dataset{initialUtxo, transactionsSequence, signingKey}
 where
  thrd (_, _, c) = c

  generateOneTransfer ::
    (Utxo, (VerificationKey PaymentKey, SigningKey PaymentKey), [CardanoTx]) ->
    Int ->
    Gen (Utxo, (VerificationKey PaymentKey, SigningKey PaymentKey), [CardanoTx])
  generateOneTransfer (utxo, (_, sender), txs) _ = do
    recipient <- genKeyPair
    -- NOTE(AB): elements is partial, it crashes if given an empty list, We don't expect
    -- this function to be ever used in production, and crash will be caught in tests
    txin <- elements $ utxoPairs utxo
    case mkSimpleCardanoTx txin (mkVkAddress networkId (fst recipient), balance @CardanoTx utxo) sender of
      Left e -> error $ "Tx construction failed: " <> show e
      Right tx ->
        pure (utxoFromTx tx, recipient, tx : txs)

mkCredentials :: Int -> (VerificationKey PaymentKey, SigningKey PaymentKey)
mkCredentials = generateWith genKeyPair
