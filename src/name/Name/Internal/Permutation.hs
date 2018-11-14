{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Name.Internal.Permutation where

import Control.Lens
import Control.Monad
import Data.Maybe
import Name.Internal.Trie
import Prelude hiding (elem, lookup)
import Data.Semigroup (Semigroup(..))

newtype Tree = Tree (Trie Atom)
  deriving (Eq,Show)

permTree :: Tree -> Atom -> Atom
permTree (Tree t) a = fromMaybe a $ lookup a t

squareTree :: Tree -> Tree
squareTree (Tree t) = Tree $ ifilterMap go t where
  go i j = mfilter (i/=) $ lookup j t -- check this

supTree :: Tree -> Maybe Atom
supTree (Tree t) = sup t

instance Semigroup Tree where
  --  x       y        z
  --  ----    ----     ------
  --  0->1             0 -> 2
  --  1->0    1->2     1 -> 0
  --          2->1     2 -> 1
  Tree x <> yt@(Tree y) = Tree $ ifilterMap f $ union (permTree yt <$> x) y where
    f i = mfilter (i/=) . pure

elem :: Atom -> Lens' Tree Atom
elem i f (Tree s) = Tree <$> at i (non i f) s where

instance Monoid Tree where
  mempty = Tree Empty

data Permutation = Permutation Tree Tree
  deriving Show

instance Eq Permutation where
  Permutation x _ == Permutation y _ = x == y

-- instance Ord Permutation where
--  Permutation x _ `compare` Permutation y _ = compare x y

instance AsEmpty Permutation where
  _Empty = prism (const mempty) $ \case
    Permutation (Tree Empty) _ -> Right ()
    t -> Left t


inv :: Permutation -> Permutation
inv (Permutation s t) = Permutation t s

square :: Permutation -> Permutation
square (Permutation s t) = Permutation (squareTree s) (squareTree t)

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

invTree :: Tree -> Tree
invTree (Tree x) = Tree $ ifoldr (flip insert) Empty x where

promote :: Tree -> Permutation
promote t = Permutation t (invTree t)
