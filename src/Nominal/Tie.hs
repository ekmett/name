{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveGeneric #-}
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

module Nominal.Tie where

import Control.Lens hiding (to, from,(#))
import GHC.Generics
import Nominal.Atom
import Nominal.Category
import Nominal.Class
import Nominal.Support

-- tie is a fully faithful functor from Nom -> Nom
-- unmap :: Nom (Tie a) (Tie b) -> Nom a b

data Tie a = Tie !Atom a
  deriving (Show, Functor, Foldable, Traversable)

instance (Eq a, Nominal a) => Eq (Tie a) where
  Tie a as == Tie b bs = trans c a as == trans c b bs where
    c = fresh (a, b, as, bs)

instance Permutable a => Permutable (Tie a) where
  trans i j (Tie a b) = Tie (trans i j a) (trans i j b)
  {-# inline trans #-}
  perm s (Tie a b) = Tie (perm s a) (perm s b)
  {-# inline perm #-}

instance Permutable1 Tie where
  perm1 f s (Tie a b) = Tie (perm s a) (f s b)
  {-# inline perm1 #-}
  trans1 f i j (Tie a b) = Tie (trans i j a) (f i j b)
  {-# inline trans1 #-}

instance Nominal a => Nominal (Tie a) where
  a # Tie b x = a == b || a # x
  {-# inline (#) #-}
  equiv = equiv . supp
  {-# inline equiv #-}
  fresh (Tie a _) = a
  {-# inline fresh #-}
  supp (Tie a b) = case supp b of
    Supp xs -> Supp $ xs & at a .~ Nothing -- merge that element into U
  {-# inline supp #-}

instance Nominal1 Tie where
  supp1 f (Tie a b) = case f b of
    Supp xs -> Supp $ xs & at a .~ Nothing

-- type NominalPrism s t a b = forall p. NominalCostrong p => Nom (p a b) (p s t)
-- type NominalLens s t a b = forall p. NominalStrong p => Nom (p a b) (p s t)
-- type NominalIso s t a b = forall p. NominalProfunctor p => Nom (p a b) (p s t)

ziptie :: (NI k, Nominal x, Nominal y) => (Tie x, Tie y) `k` Tie (x, y)
ziptie = niso_ f g where
  f (Tie a as, Tie b bs) = Tie c (trans c a as, trans c b bs) where
    c = fresh (a, b, as, bs)
  g (Tie a (x,y)) = (Tie a x, Tie a y)

coziptie :: NI k => Either (Tie x) (Tie y) `k` Tie (Either x y)
coziptie = niso_ f g where
  f (Left (Tie a as)) = Tie a (Left as)
  f (Right (Tie a as)) = Tie a (Right as)
  g (Tie a (Left as)) = Left (Tie a as)
  g (Tie a (Right bs)) = Right (Tie a bs)

delta :: N k => Tie (Tie a) `k` Tie (Tie a)
delta = nom_ $ \ (Tie a (Tie b x)) -> Tie b (Tie a x)

kappa :: (N k, Nominal a) => k a (Tie a)
kappa = nom_ $ \x -> Tie (fresh $ supp x) x

-- invariant: Untie x a -- should only be constructed for a # x
data Untie a = Untie a !Atom deriving
  (Show, Generic, Generic1)

instance Permutable a => Permutable (Untie a)
instance Permutable1 Untie
instance Nominal a => Nominal (Untie a)
instance Nominal1 Untie

--class NominalFunctor f where
--  nmap :: (Nominal a, Nominal b) => Nom a b -> Nom (f a) (f b)

--instance NominalFunctor Untie where

unit :: (N k, Nominal y) => y `k` Tie (Untie y)
unit = nom_ $ \ y -> let a = fresh (supp y) in Tie a (Untie y a)

counit :: (N k, Permutable a) => Untie (Tie a) `k` a
counit = nom_ $ \(Untie (Tie d a) c) -> trans c d a

leftAdjunct :: (N k, Nominal y) => k (Untie y) x -> k y (Tie x)
leftAdjunct = nar $ \f y ->
   let a = fresh (supp y)
   in Tie a (f (Untie y a))

rightAdjunct :: (N k, Permutable x) => k y (Tie x) -> k (Untie y) x
rightAdjunct = nar $ \f (Untie y c) -> case f y of
  Tie d x -> trans c d x

pi1 :: (N k, Nominal x) => k (Untie x) x
pi1 = nom_ $ \ (Untie x _) -> x

pi2 :: (N k, Nominal x) => k (Untie x) Atom
pi2 = nom_ $ \ (Untie _ a) -> a

paired :: (NI k, Permutable x) => Untie (Tie x) `k` (Atom, x)
paired = niso_ f g where
  f (Untie (Tie a x) a') = (a', trans a' a x)
  g (a, x) = Untie (Tie a x) a
