{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language DefaultSignatures #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Name.Lattice where

import Control.Applicative (liftA2)
import qualified Data.Bits as Bits
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Data.Void

--------------------------------------------------------------------------------
-- * Join Semilattices
--------------------------------------------------------------------------------

class Join a where
  (∨) :: a -> a -> a
  default (∨) :: Semigroup a => a -> a -> a
  (∨) = (<>)

(\/) :: Join a => a -> a -> a
(\/) = (∨)

infixr 5 ∨, \/

instance Join Void

instance Join ()

instance Join Bool where
  (∨) = (||)

instance (Join a, Join b) => Join (a, b) where
  (a,b) ∨ (c,d) = (a ∨ c, b ∨ d)

instance Ord a => Join (Set a) where
  (∨) = Set.union

instance Join IntSet where
  (∨) = IntSet.union

instance Join b => Join (a -> b) where
  (∨) = liftA2 (∨)

instance Join a => Join (Maybe a) where
  (∨) = liftA2 (∨)

--------------------------------------------------------------------------------
-- * Bounded Join Semilattices
--------------------------------------------------------------------------------

class Join a => BoundedJoin a where
  bottom :: a
  default bottom :: Monoid a => a
  bottom = mempty

instance BoundedJoin () where
  bottom = ()

instance BoundedJoin Bool where
  bottom = False

instance (BoundedJoin a, BoundedJoin b) => BoundedJoin (a, b) where
  bottom = (bottom, bottom)

instance Ord a => BoundedJoin (Set a) where
  bottom = Set.empty

instance BoundedJoin IntSet where
  bottom = IntSet.empty

instance BoundedJoin b => BoundedJoin (a -> b) where
  bottom = const bottom

instance Join a => BoundedJoin (Maybe a) where
  bottom = Nothing

--------------------------------------------------------------------------------
-- * Meet Semilattices
--------------------------------------------------------------------------------

-- Meet semilattice.
-- @
-- x ∧ x = x
-- (x ∧ y) ∧ z = x ∧ (y ∧ z)
-- x ∧ y = y ∧ x
-- @
class Meet a where
  (∧) :: a -> a -> a

(/\) :: Meet a => a -> a -> a
(/\) = (∧)

infixr 7 ∧, /\

instance Meet () where
  _ ∧ _  = ()

instance Meet Void where
  (∧) = const

instance Meet Bool where
  (∧) = (&&)

instance (Meet a, Meet b) => Meet (a, b) where
  (a,b) ∧ (c,d) = (a ∧ c, b ∧ d)

instance Ord a => Meet (Set a) where
  (∧) = Set.intersection

instance Meet IntSet where
  (∧) = IntSet.intersection

instance Meet b => Meet (a -> b) where
  f ∧ g = \x -> f x ∧ g x

instance Meet a => Meet (Maybe a) where
  Nothing ∧ y = y
  x ∧ Nothing = x
  Just a ∧ Just b = Just (a ∧ b)

--------------------------------------------------------------------------------
-- * Bounded Meet Semilattices
--------------------------------------------------------------------------------

class Meet a => BoundedMeet a where
  top :: a

instance BoundedMeet () where
  top = ()

instance BoundedMeet Bool where
  top = True

instance (BoundedMeet a, BoundedMeet b) => BoundedMeet (a, b) where
  top = (top, top)

instance BoundedMeet b => BoundedMeet (a -> b) where
  top = const top

instance BoundedMeet a => BoundedMeet (Maybe a) where
  top = Just top

--------------------------------------------------------------------------------
-- * Distributive Lattices
--------------------------------------------------------------------------------

-- | Distributive lattice
-- @
-- x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z).
-- @
class (Join a, Meet a) => DistributiveLattice a

instance DistributiveLattice Void
instance DistributiveLattice ()
instance DistributiveLattice Bool
instance (DistributiveLattice a, DistributiveLattice b) => DistributiveLattice (a, b)
instance Ord a => DistributiveLattice (Set a)
instance DistributiveLattice IntSet
instance DistributiveLattice b => DistributiveLattice (a -> b)
instance DistributiveLattice a => DistributiveLattice (Maybe a)

--------------------------------------------------------------------------------
-- * Generalized Boolean Algebras
--------------------------------------------------------------------------------

-- | A Generalized Boolean Algebra (Stone 1936)
class (BoundedJoin a, DistributiveLattice a) => GBA a where
  (\\) :: a -> a -> a
  p \\ q = p ∧ xor p q
  {-# inline (\\) #-}

  xor :: a -> a -> a
  xor p q = (p \\ q) ∨ (q \\ p)
  {-# inline xor #-}
  {-# minimal xor | (\\) #-}

instance GBA () where
  _ \\ _ = ()

  xor _ _ = ()

instance GBA Bool where
  xor = Bits.xor

instance (GBA a, GBA b) => GBA (a, b) where
  (a, b) \\ (c,d) = (a \\ c, b \\ d)

  xor (a,b) (c,d) = (xor a c, xor b d)

instance Ord a => GBA (Set a) where
  (\\) = Set.difference

instance GBA IntSet where
  (\\) = IntSet.difference

instance GBA b => GBA (a -> b) where
  f \\ g = \x -> f x \\ g x
  xor f g = \x -> xor (f x) (g x)

-- instance GBA a => GBA (Maybe a) where -- kinda lame

--------------------------------------------------------------------------------
-- * Boolean algebras
--------------------------------------------------------------------------------

class (BoundedMeet a, GBA a) => Boolean a where
  neg :: a -> a
  neg p = implies p bottom

  implies :: a -> a -> a
  implies p q = neg p ∨ q

  iff :: a -> a -> a
  iff p q = implies p q ∧ implies q p

  {-# MINIMAL neg | implies #-}

instance Boolean () where
  neg _ = ()
  implies _ _ = ()
  iff _ _ = ()

instance Boolean Bool where
  neg = not
  implies = (<=)
  iff = (==)

instance (Boolean a, Boolean b) => Boolean (a, b) where
  neg (a, b) = (neg a, neg b)
  implies (a,b) (c,d) = (implies a c, implies b d)
  iff (a,b) (c,d) = (iff a c, iff b d)

instance Boolean b => Boolean (a -> b) where
  neg f = \x -> neg (f x)
  implies f g = \x -> implies (f x) (g x)
  iff f g = \x -> iff (f x) (g x)

--------------------------------------------------------------------------------
-- * Partial orders
--------------------------------------------------------------------------------

-- | Note: this is deliberately disconnected from 'Ord' semantically to avoid
-- @newtype@ clutter
class PartialOrder t where
  (⊆) :: t -> t -> Bool
  default (⊆) :: Ord t => t -> t -> Bool
  (⊆) = (<=)

le :: PartialOrder t => t -> t -> Bool
le = (⊆)

infix 4 ⊆, `le`

instance PartialOrder ()

instance PartialOrder Void

instance PartialOrder Bool

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (a,b) ⊆ (c,d) = a ⊆ c && b ⊆ d

instance (PartialOrder a, PartialOrder b) => PartialOrder (Either a b) where
  Left a ⊆ Left b   = a ⊆ b
  Right a ⊆ Right b = a ⊆ b
  _ ⊆ _ = False

instance Ord a => PartialOrder (Set a) where
  (⊆) = Set.isSubsetOf

instance PartialOrder IntSet where
  (⊆) = IntSet.isSubsetOf
