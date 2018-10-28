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
, greater -- find a fresh variable > than all existing ones 
, sup -- the greatest of the support, used when presenting standard cycles
) where

import Control.Lens
import Data.List (groupBy)
import Data.Semigroup
import Nominal.Internal.Atom
import Nominal.Internal.Permutation
import Numeric.Natural
import Prelude hiding (elem)

swap :: Atom -> Atom -> Permutation
swap (A i) (A j) = Permutation t t where t = Tip & elem j .~ i & elem i .~ j

-- | largest support member, used by 'rcycles' for extracting standard form
sup :: Permutation -> Maybe Atom
sup (Permutation t _) = A . getMax <$> supTree t

-- | All n >= greater xs do not participate. This is the start of the smallest "ray" of step size 1
greater :: Permutation -> Atom
greater (Permutation t _) = A $ maybe 0 (succ . getMax) (supTree t)

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles
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

-- | standard cyclic representation of a permutation, broken into parts
cycles :: Permutation -> [[Atom]]
cycles = reverse . rcycles

-- | standard cyclic representation of a permutation, smashed flat
cyclic :: Permutation -> [Atom]
cyclic = concat . cycles

-- | reassemble takes a standard cyclic representation smashed flat and reassembles the cycles
--
-- @
-- 'reassemble' . 'cyclic' = 'cycles'
-- 'concat' . 'reassemble' = 'id'
-- @
reassemble :: [Atom] -> [[Atom]] 
reassemble = groupBy (\(A x) (A y) -> x > y)
