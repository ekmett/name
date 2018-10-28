{-# language LambdaCase #-}
{-# language DeriveGeneric #-}
{-# language TypeFamilies #-}
{-# language BangPatterns #-}
module Nominal.Logic
( Prop
, neg, implies, iff, top
, liftB, liftB2
) where

import Control.Lens
import GHC.Generics
import Nominal.Atom
import Nominal.Class
import Nominal.Internal.Logic
import Nominal.Set

-- TODO: check my back of the envelope math

-- the finite-cofinite algebra on atoms
-- this satisfies excluded-middle, etc.
data Prop = Finite Set | Cofinite Set deriving (Generic, Eq)

instance Perm Prop
instance Nominal Prop

-- nominal
instance SetLike Prop where
  member a (Finite s)   = member a s
  member a (Cofinite s) = not (member a s)
  {-# inline member #-}

  -- nominal
  insert a (Finite s)   = Finite (insert a s)
  insert a (Cofinite s) = Cofinite (delete a s)
  {-# inline insert #-}

  singleton = Finite . singleton
  {-# inline singleton #-}

  delete a (Finite s)   = Finite (delete a s)
  delete a (Cofinite s) = Cofinite (insert a s)
  {-# inline delete #-}

  Finite p   /\ Finite q   = Finite   (p /\ q) -- pq
  Finite p   /\ Cofinite q = Finite   (p \\ q) -- p(S-q)=pS-pq=p-q
  Cofinite p /\ Finite q   = Finite   (q \\ p) -- (S-p)q=Sq-pq=q-pq=q-p
  Cofinite p /\ Cofinite q = Cofinite (p \/ q)
  -- (S-p)(S-q)=S(S-q)-p(S-q)=SS-Sq-pS-pq=S-q-p-pq=S-q-p=S-(q+p)
  {-# inline (/\) #-}

  -- nominal
  -- @p \\ q = p /\ neg q@
  Finite p   \\ Finite q   = Finite   (p \\ q)
  Finite p   \\ Cofinite q = Finite   (p /\ q)
  Cofinite p \\ Finite q   = Cofinite (p \/ q)
  Cofinite p \\ Cofinite q = Finite   (q \\ p)
  {-# inline (\\) #-}

  -- nominal
  xor (Finite p) (Cofinite q)   = Cofinite (p /\ q)
  xor (Cofinite p) (Finite q)   = Cofinite (p /\ q)
  xor (Finite p) (Finite q)     = Finite  (xor p q)
  xor (Cofinite p) (Cofinite q) = Finite  (xor p q)
  {-# inline xor #-}

instance Semigroup Prop where
  Finite p   <> Finite q   = Finite   (p \/ q)
  Finite p   <> Cofinite q = Finite   (q \\ p)
  Cofinite p <> Finite q   = Finite   (p \\ q)
  Cofinite p <> Cofinite q = Cofinite (p /\ q)
  {-# inline (<>) #-}

instance Monoid Prop where
  mempty = Finite mempty

instance NominalSemigroup Prop

instance NominalMonoid Prop

-- | complement
neg :: Prop -> Prop
neg (Finite s) = Cofinite s
neg (Cofinite s) = Finite s
{-# inline neg #-}

-- |
-- @implies p q = ~p \/ q@
implies :: Prop -> Prop -> Prop
implies (Finite p) (Finite q)     = Finite   (p \\ q)
implies (Finite p) (Cofinite q)   = Cofinite (p /\ q)
implies (Cofinite p) (Finite q)   = Finite   (p \/ q)
implies (Cofinite p) (Cofinite q) = Finite   (q \\ p)
{-# inline implies #-}

-- |
-- @
-- iff p q = implies p q `and` implies q p
-- @
-- iff p q = not (xor p q)
-- iff p q = ite f g (neg g)
iff :: Prop -> Prop -> Prop
iff (Finite p)   (Finite q)   = Cofinite (xor p q)
iff (Finite p)   (Cofinite q) = Finite   (p /\ q)
iff (Cofinite p) (Cofinite q) = Cofinite (xor p q)
iff (Cofinite p) (Finite q)   = Finite   (p /\ q)
{-# inline iff #-}

top :: Prop
top = Cofinite mempty

instance AsEmpty Prop where
  _Empty = prism (const (Finite mempty)) $ \case
     Finite Empty -> Right ()
     t -> Left t
  {-# inline _Empty #-}

type instance Index Prop = Atom
instance Contains Prop where
  contains a f (Finite s) = Finite <$> contains a f s
  contains a f (Cofinite s) = Cofinite <$> contains a (fmap not . f . not) s
  {-# inline contains #-}

-- lift a unary boolean function
liftB :: (Bool -> Bool) -> Prop -> Prop
liftB f !s
  | f False   = if f True then top else neg s
  | otherwise = if f True then s else bottom

table :: Fun -> Prop -> Prop -> Prop
table TNever  _ _ = bottom
table TAnd    f g = f /\ g
table TGt     f g = f \\ g -- f > g
table TF      f _ = f
table TLt     f g = g \\ f -- f < g
table TG      _ g = g
table TXor    f g = xor f g
table TOr     f g = f \/ g -- f || g
table TNor    f g = neg f /\ neg g -- nor f g
table TXnor   f g = iff f g -- f /\ g \/ neg f /\ neg g
table TG'     _ g = neg g
table TGe     f g = implies g f -- f /\ neg g  -- f >= g
table TF'     f _ = neg f
table TLe     f g = implies f g -- ite f g One        -- f <= g
table TNand   f g = neg (f /\ g) -- ite f (neg g) One  -- nand f g
table TAlways _ _ = top

-- | lift boolean functions through the table e.g. @liftB2 (&&)@, @liftB2 (<=)@
liftB2 :: (Bool -> Bool -> Bool) -> Prop -> Prop -> Prop
liftB2 = table . fun

-- instance Bits Prop
