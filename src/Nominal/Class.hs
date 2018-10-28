{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
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

module Nominal.Class
( Perm(..)
, Perm1(..)
, Nominal(..)
, (#), support
, NominalSemigroup
, NominalMonoid
-- * Generics
, GPerm
, GPerm1
) where

import Control.Lens hiding (to, from, (#))
import Data.Functor.Contravariant.Generic
import Data.Proxy
import Data.Void
import GHC.Generics
import Nominal.Internal.Atom
import Nominal.Internal.Permutation
import Nominal.Internal.Set
import Nominal.Support
import Prelude hiding (elem)

class GPerm f where
  gperm :: Permutation -> f a -> f a

instance Perm c => GPerm (K1 i c) where
  gperm p (K1 a) = K1 (perm p a)

instance GPerm f => GPerm (M1 i c f) where
  gperm p (M1 a) = M1 (gperm p a)

instance GPerm V1 where
  gperm _ !v = case v of {}

instance GPerm U1 where
  gperm _ U1 = U1
  
instance (GPerm f, GPerm g) => GPerm (f :*: g) where
  gperm p (a :*: b) = gperm p a :*: gperm p b

instance (GPerm f, GPerm g) => GPerm (f :+: g) where
  gperm p (L1 a) = L1 (gperm p a)
  gperm p (R1 a) = R1 (gperm p a)

instance (Perm1 f, GPerm g) => GPerm (f :.: g) where
  gperm p (Comp1 a) = Comp1 (perm1 gperm p a)

class GPerm1 f where
  gperm1 :: (Permutation -> a -> a) -> Permutation -> f a -> f a

instance Perm c => GPerm1 (K1 i c) where
  gperm1 _ p (K1 a) = K1 (perm p a)

instance GPerm1 f => GPerm1 (M1 i c f) where
  gperm1 f p (M1 a) = M1 (gperm1 f p a)

instance GPerm1 V1 where
  gperm1 _ _ !v = case v of {}

instance GPerm1 U1 where
  gperm1 _ _ U1 = U1
  
instance (GPerm1 f, GPerm1 g) => GPerm1 (f :*: g) where
  gperm1 f p (a :*: b) = gperm1 f p a :*: gperm1 f p b

instance (GPerm1 f, GPerm1 g) => GPerm1 (f :+: g) where
  gperm1 f p (L1 a) = L1 (gperm1 f p a)
  gperm1 f p (R1 a) = R1 (gperm1 f p a)

instance (Perm1 f, GPerm1 g) => GPerm1 (f :.: g) where
  gperm1 f p (Comp1 a) = Comp1 (perm1 (gperm1 f) p a)

instance GPerm1 Par1 where
  gperm1 f p (Par1 a) = Par1 (f p a)

instance Perm1 f => GPerm1 (Rec1 f) where
  gperm1 f p (Rec1 a) = Rec1 (perm1 f p a)

class Perm s where
  perm :: Permutation -> s -> s
  default perm :: (Generic s, GPerm (Rep s)) => Permutation -> s -> s
  perm p = to . gperm p . from

instance Perm Atom where 
  perm (Permutation t _) (A i) = A (t^.elem i)

instance Perm Permutation where
  -- using this action so we can be nominal
  perm p t = inv p <> t <> p

-- efficient permutations by simultaneous induction on the set and the permutation
-- should be good for mostly small permutations or small sets
instance Perm Set where
  perm (Permutation p0 _) t0 = go 0 1 p0 t0 t0 where
    go _ _ Tip _ t = t -- outside P, no changes to S
    -- | we're in P \ S, any elements here being sent into S are deletes, use del from here on out
    --   as the entire remaining sub-tree is contained in P \ S 
    go n s (Bin _ _ j l r) STip           t -- no set left, all things down here are deletes
      | n == j    = del n'' s' r $ del n' s' l t
      | otherwise = del n'' s' r $ del n' s' l $ delete (A j) t
      where n'=n+s;n''=n'+s;s'=s+s
    go n s (Bin _ _ j l r) (SBin d sl sr) t
      | n == j    = go n'' s' r sr $ go n' s' l sl t -- outside P
      | d == 0    = go n'' s' r sr $ go n' s' l sl $ insert (A j) t -- d == 0, an element of the set, insert image
      | otherwise = go n'' s' r sr $ go n' s' l sl $ delete (A j) t -- d /= 0, not an element of the set, delete image
      where n'=n+s;n''=n'+s;s'=s+s
    del _ _ Tip t = t
    del n s (Bin _ _ j l r) t
      | n == j    = del n'' s' r $ del n' s' l t
      | otherwise = del n'' s' r $ del n' s' l $ delete (A j) t
      where n'=n+s;n''=n'+s;s'=s+s

instance Perm Void
instance Perm ()
instance (Perm a, Perm b) => Perm (a, b)
instance (Perm a, Perm b) => Perm (Either a b)
instance Perm a => Perm [a]
instance Perm a => Perm (Maybe a)
instance Perm (Proxy a)

class Perm1 f where
  perm1 :: (Permutation -> s -> s) -> Permutation -> f s -> f s
  default perm1 :: (Generic1 f, GPerm1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
  perm1 f p = to1 . gperm1 f p . from1

instance Perm1 Proxy
instance Perm1 [] 
instance Perm1 Maybe
instance Perm a => Perm1 ((,)a)
instance Perm a => Perm1 (Either a)

class Perm s => Nominal s where
  supp :: s -> Set
  default supp :: Deciding Nominal s => s -> Set
  supp = getSupported $ deciding (Proxy :: Proxy Nominal) (Supported supp)

  -- should this provide how to distribute/collect Tie as well?

instance Nominal Permutation where
  supp (Permutation t0 _) = go t0 where
    go Tip = STip
    go (Bin _ i _ l r) = SBin i (go l) (go r)

instance Nominal a => Nominal [a]

instance Nominal a => Nominal (Maybe a)

instance Nominal (Proxy a) where
  supp = mempty

instance Nominal Atom where
  supp = singleton

instance Nominal Void

instance Nominal ()

instance Nominal Set where
  supp = id

instance (Nominal a, Nominal b) => Nominal (a, b)
instance (Nominal a, Nominal b) => Nominal (Either a b)

(#) :: Nominal a => Atom -> a -> Bool
a # x = member a (supp x) -- could be more efficient

support :: Nominal a => Supported a
support = Supported supp

-- | (<>) is a nominal morphism, @a@ is a semigroup in @Nom_fs@
--
-- This implies perm is a distributive group action
--
-- @
-- perm p (a <> b) = perm p a <> perm p b
-- supp (a <> b) `isSubsetOf` (supp a <> supp b)
-- @
--
class (Nominal a, Semigroup a) => NominalSemigroup a where
instance NominalSemigroup Set
instance (NominalSemigroup a, NominalSemigroup b) => NominalSemigroup (a, b)
  
-- | perm is a unital group action
--
-- @
-- perm p mempty = mempty
-- supp mempty = mempty -- mempty has empty support
-- @
class (NominalSemigroup a, Monoid a) => NominalMonoid a
instance NominalMonoid Set
instance (NominalMonoid a, NominalMonoid b) => NominalMonoid (a, b)
