{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -funbox-strict-fields -fno-warn-orphans -fno-warn-type-defaults -O2 #-}
#ifdef ST_HACK
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Internal.Trie
{-
  ( Trie
  , singleton
  , empty
  , insert
  , lookup
  , delete
  , member
  , fromList
  , sup
  , unionWith
  , union
  , intersectionWith
  , intersection
  , diff
  ) -} where

import Control.Arrow ((***))
import Control.Applicative hiding (empty)
import Control.Lens
import Control.Monad
import Data.Coerce
import Data.Discrimination.Grouping
import Data.Foldable
import Data.Functor.Bind
import Data.Functor.Classes
import Data.Maybe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import GHC.Types
import Numeric.Natural
import Prelude hiding (lookup, length, foldr)

newtype Name = Name Natural deriving (Eq,Num,Ord)

instance Grouping Name where
  grouping = contramap coerce (grouping :: Group Natural)
  {-# inlineable grouping #-}

instance Show Name where
  showsPrec d (Name n) = showsPrec d n
  {-# inlineable showsPrec #-}

newtype Trie v = Trie { runTrie :: Map Name v } deriving
  ( Eq, Ord, Show
  , Functor, Foldable, Traversable
  , Eq1, Ord1, Show1
  , Apply, Bind
  )

sup :: Trie a -> Maybe Name
sup = fmap (fst . fst) . Map.maxViewWithKey . runTrie
{-# inlineable sup #-}

instance FunctorWithIndex Name Trie where
  imap f (Trie m) = Trie (imap f m)
  {-# inlineable imap #-}

instance FoldableWithIndex Name Trie where
  ifoldMap f (Trie m) = ifoldMap f m
  {-# inlineable ifoldMap #-}

instance TraversableWithIndex Name Trie where
  itraverse f (Trie m) = Trie <$> itraverse f m
  {-# inlineable itraverse #-}

insert :: Name -> v -> Trie v -> Trie v
insert a v (Trie m) = Trie (Map.insert a v m)
{-# inlineable insert #-}

instance Semigroup a => Semigroup (Trie a) where
  Trie a <> Trie b = Trie (Map.unionWith (<>) a b)
  {-# inlineable (<>) #-}

instance Semigroup a => Monoid (Trie a) where
  mempty = Trie mempty
  {-# inlineable mempty #-}

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f (Trie a) (Trie b) = Trie $ Map.unionWith f a b
{-# inlineable unionWith #-}

unionWithKey :: (Name -> a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWithKey f (Trie a) (Trie b) = Trie $ Map.unionWithKey f a b
{-# inlineable unionWithKey #-}

union :: Trie a -> Trie a -> Trie a
union (Trie a) (Trie b) = Trie (Map.union a b)
{-# inlineable union #-}

intersection :: Trie a -> Trie b -> Trie a
intersection (Trie a) (Trie b) = Trie (Map.intersection a b)
{-# inlineable intersection #-}

-- segfaults
intersectionWith :: (a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWith f (Trie a) (Trie b) = Trie $ Map.intersectionWith f a b
{-# inlineable intersectionWith #-}

intersectionWithKey :: (Name -> a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWithKey f (Trie a) (Trie b) = Trie $ Map.intersectionWithKey f a b
{-# inlineable intersectionWithKey #-}

filterMap :: (a -> Maybe b) -> Trie a -> Trie b
filterMap f (Trie m) = Trie (Map.mapMaybe f m)
{-# inlineable filterMap #-}

ifilterMap :: (Name -> a -> Maybe b) -> Trie a -> Trie b
ifilterMap f (Trie m) = Trie (Map.mapMaybeWithKey f m)
{-# inlineable ifilterMap #-}

filter :: (a -> Bool) -> Trie a -> Trie a
filter f (Trie m) = Trie (Map.filter f m)
{-# inlineable filter #-}

ifilter :: (Name -> a -> Bool) -> Trie a -> Trie a
ifilter f (Trie m) = Trie (Map.filterWithKey f m)
{-# inlineable ifilter #-}

partition :: (a -> Bool) -> Trie a -> (Trie a, Trie a)
partition f (Trie m) = (Trie *** Trie) $ Map.partition f m
{-# inlineable partition #-}

ipartition :: (Name -> a -> Bool) -> Trie a -> (Trie a, Trie a)
ipartition f (Trie m) = (Trie *** Trie) $ Map.partitionWithKey f m
{-# inlineable ipartition #-}

diff :: Trie a -> Trie b -> Trie a
diff (Trie m) (Trie n) = Trie (Map.difference m n)
{-# inlineable diff #-}

delete :: Name -> Trie v -> Trie v
delete !k (Trie m) = Trie (Map.delete k m)
{-# inlineable delete #-}

(!) :: Trie v -> Name -> v
(!) (Trie m) a = m Map.! a
{-# inlineable (!) #-}

lookup :: Name -> Trie v -> Maybe v
lookup a (Trie m) = Map.lookup a m
{-# inlineable lookup #-}

member :: Name -> Trie v -> Bool
member a (Trie m) = Map.member a m
{-# inlineable member #-}

-- | Build a singleton Trie
singleton :: Name -> v -> Trie v
singleton a v = Trie (Map.singleton a v)
{-# inlineable singleton #-}

fromList :: [(Name,v)] -> Trie v
fromList = Trie . Map.fromList
{-# inlineable fromList #-}

fromDistinctAscList :: [(Name,v)] -> Trie v
fromDistinctAscList = Trie . Map.fromDistinctAscList
{-# inlineable fromDistinctAscList #-}

empty :: Trie a
empty = Trie Map.empty
{-# inlineable empty #-}

type instance Index (Trie a) = Name
type instance IxValue (Trie a) = a
instance Ixed (Trie a)
instance At (Trie a) where
  at i f (Trie m) = Trie <$> at i f m
  {-# inline at #-}

instance AsEmpty (Trie a) where
  _Empty = prism (const (Trie mempty)) $ \m -> if null m then Right () else Left m
  {-# inline _Empty #-}

disjoint :: Trie a -> Trie b -> Bool
disjoint m n = null (intersection m n)
{-# inlineable disjoint #-}

imerge
  :: (Name -> a -> b -> Maybe c)
  -> (Trie a -> Trie c)
  -> (Trie b -> Trie c)
  -> Trie a -> Trie b -> Trie c
imerge f g h (Trie m) (Trie n) = Trie (Map.mergeWithKey f (coerce g) (coerce h) m n)
{-# inlineable imerge #-}

isSubtrieOfBy :: (a -> b -> Bool) -> Trie a -> Trie b -> Bool
isSubtrieOfBy f (Trie a) (Trie b) = Map.isSubmapOfBy f a b
{-# inlineable isSubtrieOfBy #-}

isSubtrieOf :: Eq a => Trie a -> Trie a -> Bool
isSubtrieOf (Trie a) (Trie b) = Map.isSubmapOf a b
{-# inline isSubtrieOf #-}
