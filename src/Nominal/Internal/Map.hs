
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Internal.Map where

import Control.Lens hiding ((#))
import Data.Functor.Compose
import Nominal.Class
import qualified Nominal.Internal.Trie as Trie
import Nominal.Internal.Trie (Trie(..), Atom)
import Nominal.Support

-- maps from atoms to values, contains a memoized approximate support
data Map a = Map !Support !(Trie a)

-- nominal
union :: NominalSemigroup a => Map a -> Map a -> Map a
union (Map s0a t0a) (Map s0b t0b) = Map (s0a <> s0b) (t0a <> t0b) where

instance NominalSemigroup a => Semigroup (Map a) where
  (<>) = union

instance NominalSemigroup a => Monoid (Map a) where
  mempty = Map mempty Empty

instance NominalSemigroup a => NominalSemigroup (Map a)
instance NominalSemigroup a => NominalMonoid (Map a)

-- requires a nominal morphism, if so, nominal
intersectionWith :: (a -> b -> c) -> Map a -> Map b -> Map c
intersectionWith f (Map s0 t0) (Map s1 t1) = case Trie.intersectionWith f t0 t1 of
  Empty -> Map mempty Empty
  t     -> Map (s0 <> s1) t

-- nominal
intersection :: Map a -> Map a -> Map a
intersection (Map s0 t0) (Map _ t1) = case Trie.intersection t0 t1 of
  Empty -> Map mempty Empty
  t     -> Map s0 t

-- nominal
diff :: Nominal s => Map a -> s -> Map a
diff (Map s0 t0) (supp -> Supp t1) = case Trie.diff t0 t1 of
  Empty -> Map mempty Empty
  t -> Map s0 t

-- nominal
(\\) :: Nominal s => Map a -> s -> Map a
(\\) = diff

-- nominal
lookup :: Atom -> Map a -> Maybe a
lookup i (Map _ t) = Trie.lookup i t

-- nominal
delete :: Atom -> Map a -> Map a
delete i (Map s0 t0) = case Trie.delete i t0 of
  Empty -> Map mempty Empty
  t -> Map s0 t

-- nominal
insert :: Nominal a => Atom -> a -> Map a -> Map a
insert v a (Map s t) = Map (supp v <> supp a <> s) $ Trie.insert v a t

-- nominal
singleton :: Nominal a => Atom -> a -> Map a
singleton v a = Map (supp v <> supp a) (Trie.singleton v a)

type instance Index (Map a) = Atom
type instance IxValue (Map a) = a
instance Nominal a => Ixed (Map a)
instance Nominal a => At (Map a) where
  at a0 f0 (Map s0 t0) = tweak <$> getCompose (at a0 (Compose . fmap diag . f0) t0) where
    diag a = (a,a)
    tweak (_, Empty)  = Map mempty Empty
    tweak (Just a,t)  = Map (supp a0 <> supp a <> s0) t
    tweak (Nothing,t) = Map s0 t

instance AsEmpty (Map a) where
  _Empty = prism (const (Map mempty Empty)) $ \case
    Map _ Empty -> Right ()
    t           -> Left t

-- nominal, clean up the cached support
trim :: Nominal a => Map a -> Map a
trim (Map _ t0) = Map (Supp (() <$ t0) <> foldMap supp t0) t0

instance Permutable1 Map where
  perm1 f p (Map s t) = Map (perm p s) (perm1 f p t)
  trans1 f i j (Map s t) = Map (trans i j s) (trans1 f i j t)

instance Permutable a => Permutable (Map a) where
  perm p (Map s t) = Map (perm p s) (perm p t)
  trans i j (Map s t) = Map (trans i j s) (trans i j t)

instance Permutable a => Nominal (Map a) where
  a # (Map s _) = a # s
  supp (Map s _) = s
  equiv (Map s _) = equiv s
  fresh (Map s _) = fresh s

