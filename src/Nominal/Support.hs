{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Support where

import Control.Lens hiding (set, sets)
import qualified Data.List as List
import Data.Discrimination.Grouping
import qualified GHC.Exts as Exts
import GHC.Generics
import Data.Void
import Nominal.Lattice
import Nominal.Internal.Permutation
import Nominal.Internal.Trie as Trie
import Nominal.Set as Set

-- morally, this is Eq a => Trie a -> Support, but we use Ord for efficiency
data Support where
  Supp :: (Eq a, Grouping a) => Trie a -> Support

instance Show Support where
  showsPrec d xs = showParen (d > 10) $
     showString "Supp " . showsPrec 11 (canonical xs)

-- | the finest support compatible with this support
-- this is a local top
finest :: Support -> Support
finest (Supp xs) = Supp (imap const xs)

-- | This is a "local" coarsest for a given set of elements
--
-- @coarsest . set = id@
coarsest :: Support -> Set
coarsest (Supp xs) = Set (() <$ xs)

permutation :: Permutation -> Support
permutation (Permutation (Tree t) _) = Supp t

sets :: Support -> [Set]
sets (Supp t) = Exts.fromList <$> runGroup grouping (ifoldr (\i a r -> (a, i): r) [] t)

{-
-- internals
-- this is really inefficient and would be nice to replace.
-- use discrimination?
sets :: Support -> [Set]
sets (Supp t0) = go t0 where
  go t = case preview folded t of
    Nothing -> []
    Just a -> case Trie.partition (a==) t of
      (l, r) -> Set (() <$ l) : go r
-}

unsets :: [Set] -> Support
unsets = Supp . ifoldr (\i (Set t) r -> Trie.union (i <$ t) r) Empty

-- meets compute coarser supports
instance Meet Support where
  xs0 ∧ ys0 = unsets $ go (sets xs0) (sets ys0) where
    go _ [] = []
    go [] ys = ys
    go (x:xs) ys = go1 x xs ys
    go1 x xs ys = case List.partition (Set.disjoint x) ys of
      (_, []) -> x : go xs ys
      (ys', foldr (∨) x -> x') -> go1 x' ys' xs

-- joins compute finer grained supports on a set of elements
instance Join Support where
  Supp xs ∨ Supp ys = Supp $ -- canonical $ Supp $
    imerge (\_ x y -> Just $ These x y) (fmap This) (fmap That) xs ys

-- bottom is the finest grained support
instance BoundedJoin Support where
  bottom = Supp (Empty :: Trie Void)

-- this is a sign that i may have support upside down!
instance Semigroup Support where
  (<>) = (∨)

instance Monoid Support where
  mempty = bottom

data These a b = This a | That b | These a b
  deriving (Generic, Eq, Ord, Show, Grouping)

flop :: a -> b -> [(b,a)] -> [(b,a)]
flop k v r = (v,k):r

canonical :: Support -> [[Atom]] -- Trie Int
canonical (Supp xs) = runGroup grouping $ ifoldr flop [] xs
{-
canonical (Supp xs) = evalState (traverse go xs) (0 :: Int, mempty) where
  go :: Ord x => x -> State (Int, Map x Int) Int
  go x = use (_2.at x) >>= \case
    Just x' -> pure x'
    Nothing -> do
      x' <- _1 <+= 1
      _2.at x ?= x'
      pure x'
-}

instance PartialOrder Support where
  -- {{x,y},{z},U-{x,y,z}} ⊆ {{x,y},U-{x,y}}
  -- {{x},{y},U-{x,y}} ⊆ {{x,y},U-{x,y}}
  -- But {{x},U-{x}} is not ⊆ {{x,y},U-{x,y}}
  Supp xs ⊆ Supp ys = null (diff ys xs)
                   && all similar (runGroup grouping $ ifoldr flop [] xs) where
    similar zs = all (\p-> z== ys^.at p) zs where
      z = ys^.at (head zs)

{-
    cond2 = snd $ execState (itraverse_ go xs) (Map.empty, True)
    -- go :: (Ord x, Ord y) => Atom -> x -> State (Map x (Maybe y), Bool) ()
    go n x = use (_1.at x) >>= \case
      Just my' | my' == my -> pure ()
               | otherwise -> _2 .= False
      Nothing -> _1.at x ?= my
      where my = ys^.at n
-}

instance Eq Support where
  xs == ys = canonical xs == canonical ys

-- (↑) :: Support -> Set -> Support
-- x ↑ y = x ∨ set y

sans :: Support -> Set -> Support
sans (Supp xs) (Set ys) = Supp (Trie.diff xs ys)
