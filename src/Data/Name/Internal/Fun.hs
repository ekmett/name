{-# language ViewPatterns #-}
{-# language DeriveGeneric #-}
{-# language DeriveDataTypeable #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Internal.Fun where

import Data.Bits (Bits, FiniteBits)
import qualified Data.Bits as Bits
import Data.Data
import GHC.Generics
import GHC.Arr
import Data.Name.Lattice

-- | all two argument functions enumerated by truth tables
data Fun = TNever | TAnd | TGt | TF | TLt | TG | TXor | TOr | TNor | TXnor | TG' | TGe | TF' | TLe | TNand | TAlways
  deriving (Eq,Ord,Show,Read,Ix,Enum,Bounded,Data,Generic)

instance Join Fun where
  f ∨ g = toEnum (fromEnum f Bits..|. fromEnum g)

instance BoundedJoin Fun where
  bottom = TNever

instance Meet Fun where
  f ∧ g = toEnum (fromEnum f Bits..&. fromEnum g)

instance BoundedMeet Fun where
  top = TAlways

instance DistributiveLattice Fun

instance GBA Fun where
  p \\ q = p ∧ neg q
  xor f g = toEnum (fromEnum f `Bits.xor` fromEnum g)

instance Boolean Fun where
  implies p q = neg p ∨ q
  neg f = toEnum (Bits.complement (fromEnum f) Bits..&. 15)

instance Bits Fun where
  (.&.) = (∧)
  (.|.) = (∨)
  xor = xor
  complement = neg
  shift x i = toEnum (Bits.shift (fromEnum x) i Bits..&. 15)
  rotateL (fromEnum -> x) i = toEnum $ (Bits.shiftL x i Bits..|. Bits.shiftR x (4 - i)) Bits..&. 15
  rotateR (fromEnum -> x) i = toEnum $ (Bits.shiftR x i Bits..|. Bits.shiftL x (4 - i)) Bits..&. 15
  bit i = toEnum (Bits.bit i Bits..&. 15)
  testBit = Bits.testBit . fromEnum
  setBit x i = toEnum (Bits.setBit (fromEnum x) i Bits..&. 15)
  clearBit x i = toEnum (Bits.clearBit (fromEnum x) i Bits..&. 15)
  bitSizeMaybe _ = Just 4
  bitSize _ = 4
  isSigned _ = False
  zeroBits = TNever
  popCount = Bits.popCount . fromEnum

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
