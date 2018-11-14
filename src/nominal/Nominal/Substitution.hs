{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language UndecidableInstances #-}

module Nominal.Substitution
( Subst(..), substgen, substexp, GSubst
, Subst1(..), subst1gen, GSubst1
) where

import Control.Lens hiding (to, from)
import Data.Maybe
import GHC.Generics
import Nominal.Atom
import Nominal.Class
import Nominal.Lattice
import Nominal.Map as Map
import Nominal.Permutation
import Nominal.Set as Set
import Nominal.Support
import Nominal.Tie

-- TODO: fuse the 'perm' call into 'subst'
-- TODO: use the 'Shared' trick from ermine or the pointer check from containers to increase term sharing.

substgen :: (Generic a, GSubst e (Rep a)) => Map e -> a -> a
substgen e = to . gsubst e . from

class Nominal e => Subst e a where
  subst :: Map e -> a -> a
  default subst :: (Generic a, GSubst e (Rep a)) => Map e -> a -> a
  subst = substgen

instance (Subst e a, Subst e b) => Subst e (a, b)
instance (Subst e a, Subst e b) => Subst e (Either a b)
instance Subst e a => Subst e [a]
instance Subst e a => Subst e (Maybe a)

subst1gen :: (Generic1 f, GSubst1 e (Rep1 f)) => (Map e -> a -> a) -> Map e -> f a -> f a
subst1gen f m = to1 . gsubst1 f m . from1

class Nominal e => Subst1 e f where
  subst1 :: (Map e -> a -> a) -> Map e -> f a -> f a
  default subst1 ::  (Generic1 f, GSubst1 e (Rep1 f)) => (Map e -> a -> a) -> Map e -> f a -> f a
  subst1 = subst1gen

class Nominal e => GSubst e f where
  gsubst :: Map e -> f a -> f a

instance Subst e c => GSubst e (K1 i c) where
  gsubst m (K1 v) = K1 (subst m v)

instance Nominal e => GSubst e V1 where
  gsubst _ v = v `seq` case v of {}

instance GSubst e f => GSubst e (M1 i c f) where
  gsubst m (M1 v) = M1 (gsubst m v)

instance Nominal e => GSubst e U1 where
  gsubst _ U1 = U1

instance (GSubst e f, GSubst e g) => GSubst e (f :*: g) where
  gsubst m (x :*: y) = gsubst m x :*: gsubst m y

instance (GSubst e f, GSubst e g) => GSubst e (f :+: g) where
  gsubst m (L1 x) = L1 (gsubst m x)
  gsubst m (R1 x) = R1 (gsubst m x)

instance (Subst1 e f, GSubst e g) => GSubst e (f :.: g) where
  gsubst m (Comp1 fgx) = Comp1 $ subst1 gsubst m fgx

class Nominal e => GSubst1 e f where
  gsubst1 :: (Map e -> a -> a) -> Map e -> f a -> f a

instance Nominal e => GSubst1 e V1 where
  gsubst1 _ _ v = v `seq` case v of {}

instance Nominal e => GSubst1 e U1 where
  gsubst1 _ _ U1 = U1

instance (GSubst1 e f, GSubst1 e g) => GSubst1 e (f :*: g) where
  gsubst1 f m (x :*: y) = gsubst1 f m x :*: gsubst1 f m y

instance (GSubst1 e f, GSubst1 e g) => GSubst1 e (f :+: g) where
  gsubst1 f m (L1 x) = L1 $ gsubst1 f m x
  gsubst1 f m (R1 x) = R1 $ gsubst1 f m x

instance (Subst1 e f, GSubst1 e g) => GSubst1 e (f :.: g) where
  gsubst1 f m (Comp1 fgx) = Comp1 $ subst1 (gsubst1 f) m fgx

instance Subst e c => GSubst1 e (K1 i c) where
  gsubst1 _ m (K1 v) = K1 (subst m v)

instance GSubst1 e f => GSubst1 e (M1 i c f) where
  gsubst1 f m (M1 v) = M1 (gsubst1 f m v)

instance Nominal e => GSubst1 e Par1 where
  gsubst1 f m (Par1 a) = Par1 (f m a)

instance Subst1 e f => GSubst1 e (Rec1 f) where
  gsubst1 f m (Rec1 x) = Rec1 (subst1 f m x)

substexp :: (Generic e, AsAtom e, GSubst e (Rep e)) => Map e -> e -> e
substexp m t = case t^?_Atom of
  Just v -> fromMaybe t $ Map.lookup v m
  Nothing -> substgen m t

instance {-# overlappable #-} 
  ( AsAtom e
  , Generic e
  , GSubst e (Rep e)
  , Nominal e -- why can't this find it via the superclass of GSubst e (Rep e)?
  ) => Subst e e where
  subst = substexp

instance {-# overlapping #-} Subst Atom Atom where subst m a = fromMaybe a $ Map.lookup a m

instance (Subst e a, Binding a, Subst e b, Nominal b) => Subst e (Tie a b) where
  subst e (Tie a b)
    | p <- fst $ Set.foldr step (mempty, fresh (e, a, b)) (bv a /\ coarsest (supp e))
    = Tie (subst e (perm p a)) (subst e (perm p b))
    where step u (x, v :- vs) = (swap u v <> x, vs)
