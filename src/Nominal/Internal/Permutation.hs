{-# language LambdaCase #-}
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

module Nominal.Internal.Permutation where

import Numeric.Natural
import Control.Lens
import Data.Semigroup
import Prelude hiding (elem)

-- the int is the depth of the shallowest free variable

-- a rather functional representation of finitely generated permutations of the naturals as trees
-- for use by nominal sets
data Tree = Tip | Bin !Natural !Int !Natural !Tree !Tree
  deriving (Show)

instance AsEmpty Tree where
  _Empty = prism (const Tip) $ \case
    Tip -> Right ()
    t -> Left t

instance Eq Tree where
  Tip == Tip = True
  Bin _ _ na la ra == Bin _ _ nb lb rb = na == nb && la == lb && ra == rb
  _ == _ = False

-- this puts trees in _some_ canonical order. good luck describing it
instance Ord Tree where
  Tip `compare` Tip = EQ
  Bin _ _ na la ra `compare` Bin _ _ nb lb rb = compare na nb <> compare la lb <> compare ra rb
  Tip `compare` Bin{} = LT
  Bin{} `compare` Tip = GT

-- used mostly for extracting standard cycle notation
supTree :: Tree -> Maybe (Max Natural)
supTree Tip = Nothing
supTree (Bin s _ _ _ _) = Just (Max s)

dep :: Tree -> Int
dep Tip = 0
dep (Bin _ i _ _ _) = i

bin :: Natural -> Natural -> Tree -> Tree -> Tree
bin i j l r = case supTree l <> supTree r of
  Nothing | i == j -> Tip -- we don't exist
          | otherwise -> Bin i 0 j l r -- we're the biggest seen so far, l and r are tips
  Just (Max m) -> Bin m (if i == j then 0 else min (dep l) (dep r) + 1) j l r

unit :: Natural -> Natural -> Natural -> Natural -> Natural -> Tree
unit t _ _ 0 i = Bin t 1 i Tip Tip -- left and right are both free, we're the largest seen so locally
unit t n s k i = case (k-1)  `divMod` 2 of
  (q,0) -> Bin t 0 n (unit t n' s' q i) Tip     -- n is free
  (q,_) -> Bin t 0 n Tip (unit t (n'+s) s' q i) -- n is free
  where n'=n+s;s'=s+s

-- TODO: avoid passing i
elem :: Functor f => Natural -> (Natural -> f Natural) -> Tree -> f Tree
elem i0 = elemx 0 1 i0 i0

elemx :: Functor f => Natural -> Natural -> Natural -> Natural -> (Natural -> f Natural) -> Tree -> f Tree
elemx n _ _ 0 f Tip             = f n <&> \n' -> bin n n' Tip Tip
elemx n _ _ 0 f (Bin _ _ j l r) = f j <&> \j' -> bin n j' l r
elemx n s i k f Tip             = f i <&> \i' -> if i == i' then Tip else unit i n s k i'
elemx n s i k f (Bin _ _ j l r) = case (k-1) `divMod` 2 of
  (q,0) -> elemx n'  s' i q f l <&> \l' -> bin n j l' r
  (q,_) -> elemx n'' s' i q f r <&> \r' -> bin n j l r'
  where n'=n+s;n''=n'+s;s'=s+s

instance Semigroup Tree where
 t0 <> t1 = go 0 1 t0 t1 where
   go _ _ Tip                Tip               = Tip
   go n s (Bin _ _ ai al ar) Tip               = bin n (t1^.elem ai) (gol n' s' al)    (gol n'' s' ar)   where n'=n+s;n''=n'+s;s'=s+s
   go n s Tip                (Bin _ _ _ bl br) = bin n (t1^.elem n)  (gor n' s' bl)    (gor n'' s' br)   where n'=n+s;n''=n'+s;s'=s+s
   go n s (Bin _ _ ai al ar) (Bin _ _ _ bl br) = bin n (t1^.elem ai) (go  n' s' al bl) (go n'' s' ar br) where n'=n+s;n''=n'+s;s'=s+s
   gol _ _ Tip = Tip
   gol n s (Bin _ _ ai al ar) = bin n (t1^.elem ai) (gol n' s' al) (gol n'' s' ar) where n'=n+s;n''=n'+s;s'=s+s
   gor _ _ Tip = Tip
   gor n s (Bin _ _ _ bl br) = bin n (t1^.elem n)  (gor n' s' bl) (gor n'' s' br) where n'=n+s;n''=n'+s;s'=s+s

instance Monoid Tree where
  mempty = Tip

-- storing both lets us invert a permutation in O(1)
data Permutation = Permutation Tree Tree
  deriving Show

instance Eq Permutation where
  Permutation x _ == Permutation y _ = x == y

instance Ord Permutation where
  Permutation x _ `compare` Permutation y _ = compare x y

instance AsEmpty Permutation where
  _Empty = prism (const mempty) $ \case
    Permutation Tip _ -> Right ()
    t -> Left t

inv :: Permutation -> Permutation
inv (Permutation s t) = Permutation t s

instance Semigroup Permutation where
  Permutation a b <> Permutation c d = Permutation (a <> c) (d <> b)

instance Monoid Permutation where
  mempty = Permutation Tip Tip
