{-# language ViewPatterns #-}
{-# language DeriveGeneric #-}
{-# language DeriveDataTypeable #-}
module Nominal.Internal.Logic where

import Data.Bits
import Data.Data
import GHC.Generics
import GHC.Arr

-- | all two argument functions enumerated by truth tables
data Fun = TNever | TAnd | TGt | TF | TLt | TG | TXor | TOr | TNor | TXnor | TG' | TGe | TF' | TLe | TNand | TAlways
  deriving (Eq,Ord,Show,Read,Ix,Enum,Bounded,Data,Generic)

instance Bits Fun where
  (.&.) f g    = toEnum (fromEnum f .&. fromEnum g)
  (.|.) f g    = toEnum (fromEnum f .|. fromEnum g)
  xor f g      = toEnum (fromEnum f `xor` fromEnum g)
  complement f = toEnum (complement (fromEnum f) .&. 15)
  shift x i = toEnum (shift (fromEnum x) i .&. 15)
  rotateL (fromEnum -> x) i = toEnum $ (shiftL x i .|. shiftR x (4 - i)) .&. 15
  rotateR (fromEnum -> x) i = toEnum $ (shiftR x i .|. shiftL x (4 - i)) .&. 15
  bit i = toEnum (bit i .&. 15)
  testBit = testBit . fromEnum
  setBit x i = toEnum (setBit (fromEnum x) i .&. 15)
  clearBit x i = toEnum (clearBit (fromEnum x) i .&. 15)
  bitSizeMaybe _ = Just 4
  bitSize _ = 4
  isSigned _ = False
  zeroBits = TNever
  popCount = popCount . fromEnum

instance FiniteBits Fun where
  finiteBitSize _ = 4

-- ite :: Prop -> Prop -> Prop -> Prop

-- enumerate as a two argument boolean function
fun :: (Bool -> Bool -> Bool) -> Fun
fun f = toEnum
  $ 8 * fromEnum (f False False)
  + 4 * fromEnum (f False True)
  + 2 * fromEnum (f True False)
  +     fromEnum (f True True)
