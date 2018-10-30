{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Permutation
( Permutation
, swap -- generator
, rcycles, cycles, cyclic, reassemble -- traditional presentation
, inv -- invert a permutation
, parity
, sign
, conjugacyClass
) where

import Control.Lens
import Control.Monad
import Data.Bits
import Data.List (groupBy, sort)
import Data.Semigroup
import Nominal.Internal.Atom
import Nominal.Internal.Permutation
import Numeric.Natural
import Prelude hiding (elem)

-- nominal
swap :: Atom -> Atom -> Permutation
swap (A i) (A j) = join Permutation $ Tip & elem j .~ i & elem i .~ j

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles. Not a nominal arrow
rcycles :: Permutation -> [[Atom]]
rcycles (Permutation t0 _) = go t0 where
  go t = case supTree t of
    Nothing -> []
    Just (Max m) -> case peel m m t of
      (t',xs) -> xs : go t'

  -- mangles the tree to remove this cycle as we go
  peel :: Natural -> Natural -> Tree -> (Tree, [Atom])
  peel m e t = case t & elem e <<.~ e of
    (n, t') | n == m    -> (t', [A e])
            | otherwise -> (A e :) <$> peel m n t'

-- | standard cyclic representation of a permutation, broken into parts. Not nominal
cycles :: Permutation -> [[Atom]]
cycles = reverse . rcycles

-- | standard cyclic representation of a permutation, smashed flat. Not nominal
cyclic :: Permutation -> [Atom]
cyclic = concat . cycles

-- | If the conjugacy class of two permutations is the same then there is a permutation that
-- can be used to conjugate one to get the other.
--
-- @
-- 'conjugacyClass' x ≡ 'conjugacyClass' y => ∃z, y = z <> x <> inv z
-- 'perm' p 'conjugacyClass' q = 'conjugacyClass' ('perm' p q) = 'conjugacyClass' q
-- @
conjugacyClass :: Permutation -> [Int]
conjugacyClass = sort . map length . rcycles

-- | reassemble takes a standard cyclic representation smashed flat and reassembles the cycles
--
-- @
-- 'reassemble' . 'cyclic' = 'cycles'
-- 'concat' . 'reassemble' = 'id'
-- 'perm' p . 'reassemble' = 'reassemble' . 'perm' p
-- @
--
reassemble :: [Atom] -> [[Atom]]
reassemble = groupBy (\(A x) (A y) -> x > y)

-- |
-- @
-- 'perm' p 'parity' q = perm p ('parity' p ('perm' (inv p) q)) = 'parity' q
-- @
parity :: Permutation -> Bool
parity = foldr (xor . foldr (const not) True) True . rcycles

-- | Determinant of the permutation matrix, nominal
sign :: Permutation -> Int
sign g = (-1) ^ fromEnum (parity g)
