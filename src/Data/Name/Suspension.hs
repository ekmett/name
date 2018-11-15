{-# language DeriveTraversable #-}
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

module Data.Name.Suspension where

import Data.Name.Class
import Data.Name.Permutation

data Suspended a = Suspended Permutation a
  deriving (Functor, Foldable, Traversable)

instance Applicative Suspended where
  pure = Suspended mempty
  Suspended mf f <*> Suspended ma a = Suspended (mf <> ma) (f a)

instance Monad Suspended where
  Suspended ma a >>= k = case k a of
    Suspended mb b -> Suspended (ma <> mb) b

instance Permutable (Suspended a) where
  perm p (Suspended q a) = Suspended (p <> q) a
  trans i j (Suspended q a) = Suspended (swap i j <> q) a

instance Nominal a => Nominal (Suspended a) where
  a # Suspended q b = perm (inv q) a # b
  supp (Suspended q a) = perm q (supp a)
  supply = supplysupp
  -- supply (Suspended q b) = perm q (supply b)
  equiv (Suspended (inv -> p) b) i j = equiv b (perm p i) (perm p j)

-- | semi-direct product of a finite permutation and a nominal semigroup
instance NominalSemigroup a => Semigroup (Suspended a) where
  Suspended p a <> Suspended q b = Suspended (p <> q) (a <> perm p b)

-- | semi-direct product of a finite permutation and a nominal monoid
instance NominalMonoid a => Monoid (Suspended a) where
  mempty = Suspended mempty mempty

-- nominal
nextract :: Permutable a => Suspended a -> a
nextract (Suspended p a) = perm p a

-- Suspended should be a nominal comonad
nduplicate :: Suspended a -> Suspended (Suspended a)
nduplicate (Suspended p a) = Suspended p (Suspended mempty a) -- we can meaningfully 'split' bijections as they don't matter in Nom
