{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language MonoLocalBinds #-}
module Nominal.Binding where

import Control.Monad
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant.Generic
import Data.Proxy
import Data.Void
import Nominal.Atom
import Nominal.Class
import Nominal.Permutation
import Nominal.Set

data Binder a = Binder { getBinder :: a -> a -> Maybe Permutation }

instance Contravariant Binder where
  contramap f (Binder g) = Binder $ \x y -> g (f x) (f y)

instance Divisible Binder where
  conquer = Binder $ \ _ _ -> Just mempty
  divide f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    (b, c) -> case f y of
       (d, e) -> (<>) <$> g b d <*> h c e

instance Decidable Binder where
  lose f = Binder $ absurd . f
  choose f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    Left b -> case f x of
      Left d -> g b d
      Right _ -> Nothing
    Right c -> case f y of
      Left _ -> Nothing
      Right e -> h c e

-- assumption: all variables in a binding are distinct
class Nominal a => Binding a where
  binding :: a -> a -> Maybe Permutation
  default binding :: Deciding Binding a => a -> a -> Maybe Permutation
  binding a b = getBinder (deciding (Proxy :: Proxy Binding) (Binder binding)) a b

  bv :: a -> Set
  default bv :: Deciding Binding a => a -> Set
  bv = getOp $ deciding (Proxy :: Proxy Binding) $ Op bv

instance Binding Atom where
  binding a b = Just (swap a b)
  bv = singleton

instance Binding () where
  binding _ _ = Just mempty
  bv = mempty

instance Binding Void where
  binding = absurd
  bv = absurd

instance Binding Int where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance Binding Bool where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance (Binding a, Binding b) => Binding (a, b)
instance (Binding a, Binding b, Binding c) => Binding (a, b, c)
instance (Binding a, Binding b, Binding c, Binding d) => Binding (a, b, c, d)
instance (Binding a, Binding b) => Binding (Either a b)
instance Binding a => Binding (Maybe a)
instance Binding a => Binding [a]

class Nominal1 f => Binding1 f where
  binding1 :: (a -> a -> Maybe Permutation) -> f a -> f a -> Maybe Permutation
  default binding1 :: Deciding1 Binding f => (a -> a -> Maybe Permutation) -> f a -> f a -> Maybe Permutation
  binding1 f a b = getBinder (deciding1 (Proxy :: Proxy Binding) (Binder binding) (Binder f)) a b

  bv1 :: (a -> Set) -> f a -> Set
  default bv1 :: Deciding1 Binding f => (a -> Set) -> f a -> Set
  bv1 f = getOp $ deciding1 (Proxy :: Proxy Binding) (Op bv) (Op f)

instance Binding a => Binding1 (Either a)
instance Binding a => Binding1 ((,) a)
instance (Binding a, Binding b) => Binding1 ((,,) a b)
instance (Binding a, Binding b, Binding c) => Binding1 ((,,,) a b c)
instance Binding1 []
instance Binding1 Maybe

-- things that would need [Permutation]:
-- Binding Set isn't really possible, it'd need to give back several possible matchings, using [Permutation] it could give back answers but not equivariantly
-- Binding Support is worse
-- Binding Permutatation -- takes permutations to permutations but would need to choose which one of each cycle of the same length was which
-- Binding1 Map
-- Binding1 Trie

-- irrefutable matches are permutation torsors?
class Binding a => Irrefutable a where
  match :: a -> a -> Permutation
  -- fresh :: Nominal b => b -> a -- this is where fresh really belongs
  -- the thing in Nominal should supply an infinite stream of fresh variables that this can consume
  -- cost: the instance for Void

instance Irrefutable Atom where
  match = swap -- TODO: move this far enough upstream so that match _is_ swap?

instance Irrefutable Void where
  match = absurd

instance Irrefutable () where
  match _ _ = mempty

instance (Irrefutable a, Irrefutable b) => Irrefutable (a, b) where
  match (a,b) (c,d) = match a c <> match b d

instance (Irrefutable a, Irrefutable b, Irrefutable c) => Irrefutable (a, b, c) where
  match (a,b,c) (d,e,f) = match a d <> match b e <> match c f

instance (Irrefutable a, Irrefutable b, Irrefutable c, Irrefutable d) => Irrefutable (a, b, c, d) where
  match (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> match d h

class Binding1 f => Irrefutable1 f where
  match1 :: (a -> a -> Permutation) -> f a -> f a -> Permutation

instance (Irrefutable a) => Irrefutable1 ((,) a) where
  match1 f (a,b) (c,d) = match a c <> f b d

instance (Irrefutable a, Irrefutable b) => Irrefutable1 ((,,) a b) where
  match1 g (a,b,c) (d,e,f) = match a d <> match b e <> g c f

instance (Irrefutable a, Irrefutable b, Irrefutable c) => Irrefutable1 ((,,,) a b c) where
  match1 i (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> i d h
