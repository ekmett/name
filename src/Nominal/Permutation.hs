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

-- import Control.Lens
import Control.Monad
import Data.Bits
import Data.List (groupBy, sort)
import Nominal.Internal.Trie (Atom(..), insert, delete, lookup, Trie(..))
import Nominal.Internal.Permutation
import Prelude hiding (elem, lookup)

-- nominal
swap :: Atom -> Atom -> Permutation
swap i j
  | i /= j = join Permutation $ Tree $ insert i j $ insert j i Nil
  | otherwise = mempty

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles. Not a nominal arrow
rcycles :: Permutation -> [[Atom]]
rcycles (Permutation t0 _) = go t0 where
  go t = case supTree t of
    Nothing -> []
    Just m -> case peel m m t of
      (t',xs) -> xs : go t'

  -- mangles the tree to remove this cycle as we go
  peel :: Atom -> Atom -> Tree -> (Tree, [Atom])
  peel m e (Tree t) = case lookup e t of
    Nothing -> error $ show (m,e,t)
    Just n | n == m -> (Tree (delete e t), [e])
           | otherwise -> (e:) <$> peel m n (Tree (delete e t))
    
{-
   case t & at e <<.~ Nothing of
    (Just n, t') | n == m    -> (Tree t', [e])
                 | otherwise -> (e :) <$> peel m n (Tree t')
    (Nothing, t') -> (Tree t', [e])
-}

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
