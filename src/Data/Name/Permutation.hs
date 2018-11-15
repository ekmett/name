{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language LambdaCase #-}

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
( Permutation(..)
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
import Data.Name.Internal.Perm
import Data.Name.Internal.Trie
import Data.Semigroup
import Prelude hiding (elem, lookup)

-- | The pair of a permutation and its inverse permutation
data Permutation = Permutation Perm Perm
  deriving Show

instance Eq Permutation where
  Permutation x _ == Permutation y _ = x == y

instance Ord Permutation where
  Permutation x _ `compare` Permutation y _ = compare x y

instance AsEmpty Permutation where
  _Empty = prism (const mempty) $ \case
    Permutation (Perm Empty) _ -> Right ()
    t -> Left t

inv :: Permutation -> Permutation
inv (Permutation s t) = Permutation t s

square :: Permutation -> Permutation
square (Permutation s t) = Permutation (square' s) (square' t)

instance Semigroup Permutation where
  Permutation a b <> Permutation c d = Permutation (a <> c) (d <> b)
  stimes n x0 = case compare n 0 of
    LT -> f (inv x0) (negate n)
    EQ -> mempty
    GT -> f x0 n
    where
      f x y
        | even y = f (square x) (quot y 2)
        | y == 1 = x
        | otherwise = g (square x) (quot y 2) x
      g x y z
        | even y = g (square x) (quot y 2) z
        | y == 1 = x <> z
        | otherwise = g (square x) (quot y 2) (x <> z)

instance Monoid Permutation where
  mempty = Permutation mempty mempty

-- promote :: Perm -> Permutation
-- promote t = Permutation t (inv' t)

-- | equivariant
swap :: Name -> Name -> Permutation
swap i j
  | i /= j = join Permutation $ Perm $ insert i j $ insert j i Empty
  | otherwise = mempty
{-# inline [0] swap #-}

-- | This is not quite natural order, as its easiest for me to find the largest element and work backwards.
-- for natural order, reverse the list of cycles. Not a nominal arrow
rcycles :: Permutation -> [[Name]]
rcycles (Permutation t0 _) = go t0 where
  go t = case sup' t of
    Nothing -> []
    Just m -> case peel m m t of
      (t',xs) -> xs : go t'

  -- mangles the tree to remove this cycle as we go
  peel :: Name -> Name -> Perm -> (Perm, [Name])
  peel m e (Perm t) = case lookup e t of
    Nothing -> error $ show (m,e,t)
    Just n | n == m -> (Perm (delete e t), [e])
           | otherwise -> (e:) <$> peel m n (Perm (delete e t))

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

-- | Reassemble takes a standard cyclic representation smashed flat and reassembles the cycles, not equivariant
--
-- @
-- 'reassemble' . 'cyclic' = 'cycles'
-- 'concat' . 'reassemble' = 'id'
-- 'perm' p . 'reassemble' = 'reassemble' . 'perm' p
-- @
--
reassemble :: [Name] -> [[Name]]
reassemble = groupBy (\(Name x) (Name y) -> x > y)

-- | Equivariant
-- 
-- @
-- 'perm' p 'parity' q = perm p ('parity' p ('perm' (inv p) q)) = 'parity' q
-- @
parity :: Permutation -> Bool
parity = foldr (xor . foldr (const not) True) True . rcycles

-- | Determinant of the permutation matrix, equivariant
sign :: Permutation -> Int
sign g = (-1) ^ fromEnum (parity g)
