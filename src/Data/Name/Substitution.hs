{-# Language EmptyCase #-}
{-# Language TypeOperators #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language FlexibleInstances #-}
{-# Language MultiParamTypeClasses #-}
{-# Language UndecidableInstances #-}
{-# Language ViewPatterns #-}

module Data.Name.Substitution
( Subst(..), substgen, substexp, GSubst
, Subst1(..), subst1gen, GSubst1
) where

import Control.Lens hiding (to, from)
import Data.Maybe
import Data.Name.Type
import Data.Name.Class
import Data.Name.Lattice
import Data.Name.Map as Map
import Data.Name.Permutation
import Data.Name.Set as Set
import Data.Name.Support
import Data.Name.Tie
import GHC.Generics

-- TODO: fuse the 'perm' call into 'subst'
-- TODO: use the 'Shared' trick from ermine or the pointer check from containers to increase term sharing.

substgen :: (Generic a, GSubst e (Rep a)) => Map e -> Permutation -> a -> a
substgen m p = to . gsubst m p . from

class Nominal e => Subst e a where
  subst :: Map e -> Permutation -> a -> a
  default subst :: (Generic a, GSubst e (Rep a)) => Map e -> Permutation -> a -> a
  subst = substgen

instance (Subst e a, Subst e b) => Subst e (a, b)
instance (Subst e a, Subst e b) => Subst e (Either a b)
instance Subst e a => Subst e [a]
instance Subst e a => Subst e (Maybe a)

subst1gen :: (Generic1 f, GSubst1 e (Rep1 f)) => (Map e -> Permutation -> a -> a) -> Map e -> Permutation -> f a -> f a
subst1gen f m p = to1 . gsubst1 f m p . from1

class Nominal e => Subst1 e f where
  subst1 :: (Map e -> Permutation -> a -> a) -> Map e -> Permutation -> f a -> f a
  default subst1 ::  (Generic1 f, GSubst1 e (Rep1 f)) => (Map e -> Permutation -> a -> a) -> Map e -> Permutation -> f a -> f a
  subst1 = subst1gen

class Nominal e => GSubst e f where
  gsubst :: Map e -> Permutation -> f a -> f a

instance Subst e c => GSubst e (K1 i c) where
  gsubst m p (K1 v) = K1 (subst m p v)

instance Nominal e => GSubst e V1 where
  gsubst _ _ v = v `seq` case v of {}

instance GSubst e f => GSubst e (M1 i c f) where
  gsubst m p (M1 v) = M1 (gsubst m p v)

instance Nominal e => GSubst e U1 where
  gsubst _ _ U1 = U1

instance (GSubst e f, GSubst e g) => GSubst e (f :*: g) where
  gsubst m p (x :*: y) = gsubst m p x :*: gsubst m p y

instance (GSubst e f, GSubst e g) => GSubst e (f :+: g) where
  gsubst m p (L1 x) = L1 (gsubst m p x)
  gsubst m p (R1 x) = R1 (gsubst m p x)

instance (Subst1 e f, GSubst e g) => GSubst e (f :.: g) where
  gsubst m p (Comp1 fgx) = Comp1 $ subst1 gsubst m p fgx

class Nominal e => GSubst1 e f where
  gsubst1 :: (Map e -> Permutation -> a -> a) -> Map e -> Permutation -> f a -> f a

instance Nominal e => GSubst1 e V1 where
  gsubst1 _ _ _ v = v `seq` case v of {}

instance Nominal e => GSubst1 e U1 where
  gsubst1 _ _ _ U1 = U1

instance (GSubst1 e f, GSubst1 e g) => GSubst1 e (f :*: g) where
  gsubst1 f m p (x :*: y) = gsubst1 f m p x :*: gsubst1 f m p y

instance (GSubst1 e f, GSubst1 e g) => GSubst1 e (f :+: g) where
  gsubst1 f m p (L1 x) = L1 $ gsubst1 f m p x
  gsubst1 f m p (R1 x) = R1 $ gsubst1 f m p x

instance (Subst1 e f, GSubst1 e g) => GSubst1 e (f :.: g) where
  gsubst1 f m p (Comp1 fgx) = Comp1 $ subst1 (gsubst1 f) m p fgx

instance Subst e c => GSubst1 e (K1 i c) where
  gsubst1 _ m p (K1 v) = K1 (subst m p v)

instance GSubst1 e f => GSubst1 e (M1 i c f) where
  gsubst1 f m p (M1 v) = M1 (gsubst1 f m p v)

instance Nominal e => GSubst1 e Par1 where
  gsubst1 f m p (Par1 a) = Par1 (f m p a)

instance Subst1 e f => GSubst1 e (Rec1 f) where
  gsubst1 f m p (Rec1 x) = Rec1 (subst1 f m p x)

substexp :: (Generic e, AsName e, GSubst e (Rep e)) => Map e -> Permutation -> e -> e
substexp m p t = case t^?_Name of
  Just (perm p -> v) -> fromMaybe (review _Name v) $ Map.lookup v m
  Nothing -> substgen m p t

instance {-# overlappable #-} 
  ( AsName e
  , Generic e
  , GSubst e (Rep e)
  , Nominal e -- why can't this find it via the superclass of GSubst e (Rep e)?
  ) => Subst e e where
  subst = substexp

instance {-# overlapping #-} Subst Name Name where
  subst m p (perm p -> a) = fromMaybe a $ Map.lookup a m

instance (Subst e a, Binding a, Subst e b, Nominal b) => Subst e (Tie a b) where
  subst m p (Tie a b)
    | p' <- fst $ Set.foldr step (p, supply (m, p, a, b)) $ bv a /\ perm (inv p) (coarsest (supp m)) -- (m,p,a,b) is conservative but cheap
    = Tie (subst m p' a) (subst m p' b)
    where step u (x, vs) = case refresh vs of
            (v,vs') -> (swap u v <> x, vs')
