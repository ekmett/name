{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language MonoLocalBinds #-}
module Nominal.Binding where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant.Generic
import Data.Proxy
import Data.Void
import Nominal.Atom
import Nominal.Class
import Nominal.Permutation

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

instance Binding Atom where 
  binding a b = Just (swap a b)

instance Binding () where binding _ _ = Just mempty
instance Binding Void where binding = absurd
instance Binding Int where binding _ _ = Just mempty
instance Binding Bool where binding _ _ = Just mempty
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
