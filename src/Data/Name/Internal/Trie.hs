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

newtype Name = Name Natural deriving (Eq,Num,Ord) -- Num,Ord only for convenience

-- TODO: lift this into discrimination for Natural/Integer?
instance Grouping Name where
  grouping = contramap coerce (grouping :: Group Natural)

instance Show Name where
  showsPrec d (Name n) = showsPrec d n

newtype Trie v = Trie { runTrie :: Map Name v } deriving
  ( Eq, Ord, Show
  , Functor, Foldable, Traversable
  , Eq1, Ord1, Show1
  -- , FunctorWithIndex Name, FoldableWithIndex Name, TraversableWithIndex Name
  -- , Apply, Bind
  )

sup :: Trie a -> Maybe Name
sup = fmap (fst . fst) . Map.maxViewWithKey . runTrie

instance FunctorWithIndex Name Trie where
  imap f (Trie m) = Trie (imap f m)

instance FoldableWithIndex Name Trie where
  ifoldMap f (Trie m) = ifoldMap f m

instance TraversableWithIndex Name Trie where
  itraverse f (Trie m) = Trie <$> itraverse f m

instance Apply Trie where
  liftF2 f (Trie m) (Trie n) = Trie (liftF2 f m n)

instance Bind Trie where
  Trie m >>- f = Trie (m >>- runTrie . f)

insert :: Name -> v -> Trie v -> Trie v
insert a v (Trie m) = Trie (Map.insert a v m)

instance Semigroup a => Semigroup (Trie a) where
  Trie a <> Trie b = Trie (Map.unionWith (<>) a b)
  {-# inlineable (<>) #-}

instance Semigroup a => Monoid (Trie a) where
  mempty = Trie mempty
  {-# inline mempty #-}

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f (Trie a) (Trie b) = Trie $ Map.unionWith f a b
{-# inline unionWith #-}

unionWithKey :: (Name -> a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWithKey f (Trie a) (Trie b) = Trie $ Map.unionWithKey f a b

union :: Trie a -> Trie a -> Trie a
union (Trie a) (Trie b) = Trie (Map.union a b)
{-# inline union #-}

intersection :: Trie a -> Trie b -> Trie a
intersection (Trie a) (Trie b) = Trie (Map.intersection a b)
{-# inline intersection #-}

-- segfaults
intersectionWith :: (a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWith f (Trie a) (Trie b) = Trie $ Map.intersectionWith f a b

intersectionWithKey :: (Name -> a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWithKey f (Trie a) (Trie b) = Trie $ Map.intersectionWithKey f a b

filterMap :: (a -> Maybe b) -> Trie a -> Trie b
filterMap f (Trie m) = Trie (Map.mapMaybe f m)

{-# inline filterMap #-}

ifilterMap :: (Name -> a -> Maybe b) -> Trie a -> Trie b
ifilterMap f (Trie m) = Trie (Map.mapMaybeWithKey f m)

filter :: (a -> Bool) -> Trie a -> Trie a
filter f (Trie m) = Trie (Map.filter f m)
{-# inline filter #-}

ifilter :: (Name -> a -> Bool) -> Trie a -> Trie a
ifilter f (Trie m) = Trie (Map.filterWithKey f m)

partition :: (a -> Bool) -> Trie a -> (Trie a, Trie a)
partition f (Trie m) = (Trie *** Trie) $ Map.partition f m
{-# inline partition #-}

ipartition :: (Name -> a -> Bool) -> Trie a -> (Trie a, Trie a)
ipartition f (Trie m) = (Trie *** Trie) $ Map.partitionWithKey f m

diff :: Trie a -> Trie b -> Trie a
diff (Trie m) (Trie n) = Trie (Map.difference m n)

delete :: Name -> Trie v -> Trie v
delete !k (Trie m) = Trie (Map.delete k m)

(!) :: Trie v -> Name -> v
(!) (Trie m) a = m Map.! a

lookup :: Name -> Trie v -> Maybe v
lookup a (Trie m) = Map.lookup a m
{-# inlineable lookup #-}

member :: Name -> Trie v -> Bool
member a (Trie m) = Map.member a m
{-# inlineable member #-}

-- | Build a singleton Trie
singleton :: Name -> v -> Trie v
singleton a v = Trie (Map.singleton a v)
{-# inline singleton #-}

fromList :: [(Name,v)] -> Trie v
fromList = Trie . Map.fromList
{-# inline fromList #-}

empty :: Trie a
empty = Trie Map.empty
{-# inline empty #-}

type instance Index (Trie a) = Name
type instance IxValue (Trie a) = a
instance Ixed (Trie a)
instance At (Trie a) where
  at i f (Trie m) = Trie <$> at i f m

instance AsEmpty (Trie a) where
  _Empty = prism (const (Trie mempty)) $ \m -> if null m then Right () else Left m

disjoint :: Trie a -> Trie b -> Bool
disjoint m n = null (intersection m n)

imerge
  :: (Name -> a -> b -> Maybe c)
  -> (Trie a -> Trie c)
  -> (Trie b -> Trie c)
  -> Trie a -> Trie b -> Trie c
imerge f g h (Trie m) (Trie n)
  = Trie (Map.mergeWithKey f (coerce g) (coerce h) m n)

isSubtrieOfBy :: (a -> b -> Bool) -> Trie a -> Trie b -> Bool
isSubtrieOfBy f (Trie a) (Trie b) = Map.isSubmapOfBy f a b

isSubtrieOf :: Eq a => Trie a -> Trie a -> Bool
isSubtrieOf (Trie a) (Trie b) = Map.isSubmapOf a b
