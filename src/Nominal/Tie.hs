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

import Control.Lens hiding (to, from)
import Nominal.Atom
import Nominal.Category
import Nominal.Class
import Nominal.Permutation
import Nominal.Support

-- tie is a fully faithful functor from Nom -> Nom

data Tie a = Tie !Atom a
  deriving (Show, Functor, Foldable, Traversable)

instance (Eq a, Nominal a) => Eq (Tie a) where
  Tie a as == Tie b bs = perm (swap c a) as == perm (swap c b) bs where
    c = fresh (supp a <> supp b <> supp as <> supp bs)

instance Permutable a => Permutable (Tie a) where
  perm s (Tie a b) = Tie (perm s a) (perm s b)

instance Permutable1 Tie where
  perm1 f s (Tie a b) = Tie (perm s a) (f s b)

instance Nominal a => Nominal (Tie a) where
  supp (Tie a b) = case supp b of
    Supp xs -> Supp $ xs & at a .~ Nothing -- merge that element into U

-- type NominalPrism s t a b = forall p. NominalCostrong p => Nom (p a b) (p s t)
-- type NominalLens s t a b = forall p. NominalStrong p => Nom (p a b) (p s t)
-- type NominalIso s t a b = forall p. NominalProfunctor p => Nom (p a b) (p s t)

ziptie :: (N k, Nominal x, Nominal y) => (Tie x, Tie y) `k` Tie (x, y)
ziptie = nom_ go where
  go (Tie a as, Tie b bs) = Tie c (perm (swap c a) as, perm (swap c b) bs) where
    c = fresh (supp a <> supp b <> supp as <> supp bs)

unziptie :: N k => Tie (x, y) `k` (Tie x, Tie y)
unziptie = nom_ $ \ (Tie a (x,y)) -> (Tie a x, Tie a y)

zipe :: N k => Either (Tie x) (Tie y) `k` Tie (Either x y)
zipe = nom_ go where
  go (Left (Tie a as)) = Tie a (Left as)
  go (Right (Tie a as)) = Tie a (Right as)

unzipe :: N k => Tie (Either x y) `k` Either (Tie x) (Tie y)
unzipe = nom_ go where
  go (Tie a (Left as)) = Left (Tie a as)
  go (Tie a (Right bs)) = Right (Tie a bs)

delta :: N k => Tie (Tie a) `k` Tie (Tie a)
delta = nom_ $ \ (Tie a (Tie b x)) -> Tie b (Tie a x)

kappa :: (N k, Nominal a) => k a (Tie a)
kappa = nom_ $ \x -> Tie (fresh $ supp x) x

-- invariant: Untie x a -- should only be constructed for a # x
data Untie a = Untie a !Atom deriving
  (Show) -- , Functor, Foldable, Traversable)

--class NominalFunctor f where
--  nmap :: (Nominal a, Nominal b) => Nom a b -> Nom (f a) (f b)

--instance NominalFunctor Untie where

unit :: (N k, Nominal y) => y `k` Tie (Untie y)
unit = nom_ $ \ y -> let a = fresh (supp y) in Tie a (Untie y a)

counit :: (N k, Permutable a) => Untie (Tie a) `k` a
counit = nom_ $ \(Untie (Tie d a) c) -> perm (swap c d) a

leftAdjunct :: (N k, Nominal y) => k (Untie y) x -> k y (Tie x)
leftAdjunct = nar $ \f y ->
   let a = fresh (supp y)
   in Tie a (f (Untie y a))

rightAdjunct :: (N k, Permutable x) => k y (Tie x) -> k (Untie y) x
rightAdjunct = nar $ \f (Untie y c) -> case f y of
  Tie d x -> perm (swap c d) x

-- @
-- hither . yon = id
-- yon . hither = id
-- @
hither :: (N k, Permutable x) => Untie (Tie x) `k` (Atom, x)
hither = nom_ $ \(Untie (Tie a x) a') -> (a', perm (swap a' a) x)

yon :: N k => (Atom, x) `k` Untie (Tie x)
yon = nom_ $ \(a, x) -> Untie (Tie a x) a

{-
class Restrictive x where
  -- |
  -- @
  -- restrict . nreturn = id
  -- restrict . fmap restrict = restrict . fmap restrict . delta
  -- restrict (Tie a x) = a -\- x
  -- @
  restrict :: Tie x -> x
  restrict (Tie a x) = a -\- x

  -- |
  -- @
  -- a # a #\ x
  -- a # x ⇒  a #\ x = x
  -- a #\ b #\ x = b #\ a #\ x
  -- @
  -- |
  (#\) :: Atom -> x -> x
  a #\ x = restrict (Tie a x)

  {-# MINIMINAL restrict | (-\-) #-}

infixr 6 -\-
-}
