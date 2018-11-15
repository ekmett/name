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

module Data.Name.Permutation
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
import Data.Name.Internal.Trie
import Data.Name.Internal.Permutation
import Prelude hiding (elem, lookup)

-- nominal
swap :: Name -> Name -> Permutation
swap i j
  | i /= j = join Permutation $ Tree $ insert i j $ insert j i Empty
  | otherwise = mempty
{-# inline [0] swap #-}

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles. Not a nominal arrow
rcycles :: Permutation -> [[Name]]
rcycles (Permutation t0 _) = go t0 where
  go t = case supTree t of
    Nothing -> []
    Just m -> case peel m m t of
      (t',xs) -> xs : go t'

  -- mangles the tree to remove this cycle as we go
  peel :: Name -> Name -> Tree -> (Tree, [Name])
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

-- | standard cyclic representation of a permutation, broken into parts. Not equivariant
cycles :: Permutation -> [[Name]]
cycles = reverse . rcycles

-- | standard cyclic representation of a permutation, smashed flat. Not equivariant
cyclic :: Permutation -> [Name]
cyclic = concat . cycles

-- | If the conjugacy class of two permutations is the same then there is a permutation that
-- can be used to conjugate one to get the other. equivariant
--
-- @
-- 'conjugacyClass' x ≡ 'conjugacyClass' y => ∃z, y = z <> x <> inv z
-- 'perm' p 'conjugacyClass' q = 'conjugacyClass' ('perm' p q) = 'conjugacyClass' q
-- @
conjugacyClass :: Permutation -> [Int]
conjugacyClass = sort . map length . rcycles

-- | reassemble takes a standard cyclic representation smashed flat and reassembles the cycles, not equivariant
--
-- @
-- 'reassemble' . 'cyclic' = 'cycles'
-- 'concat' . 'reassemble' = 'id'
-- 'perm' p . 'reassemble' = 'reassemble' . 'perm' p
-- @
--
reassemble :: [Name] -> [[Name]]
reassemble = groupBy (\(Name x) (Name y) -> x > y)

-- | equivariant
-- @
-- 'perm' p 'parity' q = perm p ('parity' p ('perm' (inv p) q)) = 'parity' q
-- @
parity :: Permutation -> Bool
parity = foldr (xor . foldr (const not) True) True . rcycles

-- | Determinant of the permutation matrix, equivariant
sign :: Permutation -> Int
sign g = (-1) ^ fromEnum (parity g)
