{-# language DeriveTraversable #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Suspension where

import Nominal.Class
import Nominal.Permutation

-- semi-direct product of a permutation and a nominal monoid
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

instance Nominal a => Nominal (Suspended a) where
  supp (Suspended q a) = perm q (supp a)

instance NominalSemigroup a => Semigroup (Suspended a) where
  Suspended p a <> Suspended q b = Suspended (p <> q) (a <> perm p b)
  
instance NominalMonoid a => Monoid (Suspended a) where
  mempty = Suspended mempty mempty

-- nominal
nextract :: Permutable a => Suspended a -> a
nextract (Suspended p a) = perm p a

-- Suspended should be a nominal comonad
nduplicate :: Suspended a -> Suspended (Suspended a)
nduplicate (Suspended p a) = Suspended p (Suspended mempty a) -- we can meaningfully 'split' bijections as they don't matter in Nom
