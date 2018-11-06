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

import GHC.Generics
import Nominal.Atom
import Nominal.Binding
import Nominal.Category
import Nominal.Class
import Nominal.Lattice
import Nominal.Set
import Nominal.Support

type (⊸) = Tie

data Tie a b = Tie a b
  deriving (Generic, Generic1, Show, Functor, Foldable, Traversable)

instance (Eq a, Binding a, Eq b, Nominal b) => Eq (Tie a b) where
  Tie a as == Tie b bs
    | a == b = as == bs
    | otherwise = case binding a b of
      Nothing -> False
      Just p   -> sep bs (bv a \\ bv b) && as == perm p bs

sep :: Nominal a => a -> Set -> Bool
sep = undefined

instance (Permutable a, Permutable b) => Permutable (Tie a b) where
  trans i j (Tie a b) = Tie (trans i j a) (trans i j b)
  {-# inline trans #-}
  perm s (Tie a b) = Tie (perm s a) (perm s b)
  {-# inline perm #-}

instance Permutable a => Permutable1 (Tie a) where
  perm1 f s (Tie a b) = Tie (perm s a) (f s b)
  {-# inline perm1 #-}
  trans1 f i j (Tie a b) = Tie (trans i j a) (f i j b)
  {-# inline trans1 #-}

instance (Binding a, Nominal b) => Nominal (Tie a b) where
  a # Tie b x = member a (bv b) || a # x
  {-# inline (#) #-}
  -- fresh (Tie a b) -- pick a member of bv a, or compute something fresh w.r.t. x, if that is empty
  -- {-# inline fresh #-}
  supp (Tie a b) = supp b `sans` bv a
  {-# inline supp #-}

instance Binding a => Nominal1 (Tie a) where
  supp1 f (Tie a b) = f b `sans` bv a

unziptie :: N k => k (a ⊸ (x, y)) (a ⊸ x, a ⊸ y)
unziptie = nom_ $ \(Tie a (x,y)) -> (Tie a x, Tie a y)

ziptie :: (NI k, Irrefutable a, Permutable y) => k (a ⊸ x, a ⊸ y) (a ⊸ (x, y))
ziptie = niso_ f unziptie where
  f (Tie a as, Tie b bs) = Tie a (as, perm (match a b) bs)

coziptie :: NI k => k (Either (a ⊸ x) (a ⊸ y)) (a ⊸ Either x y)
coziptie = niso_ f g where
  f (Left (Tie a as)) = Tie a (Left as)
  f (Right (Tie a as)) = Tie a (Right as)
  g (Tie a (Left as)) = Left (Tie a as)
  g (Tie a (Right bs)) = Right (Tie a bs)

delta :: NI k => k (a ⊸ (b ⊸ c)) (b ⊸ (a ⊸ c))
delta = niso_ (\(Tie a (Tie b c)) -> Tie b (Tie a c)) (\(Tie a (Tie b c)) -> Tie b (Tie a c))

kappa :: (N k, Nominal a, Fresh b) => k a (b ⊸ a)
kappa = nom_ $ \x -> Tie (fresh $ supp x) x

type (∙) = Untie

-- side condition: a # b
data Untie a b = Untie a b deriving (Eq, Show, Generic, Generic1)

instance (Permutable a, Permutable b) => Permutable (Untie a b)
instance Permutable a => Permutable1 (Untie a)
instance (Nominal a, Binding b) => Nominal (Untie a b)
instance Nominal a => Nominal1 (Untie a)
instance (Binding a, Binding b) => Binding (Untie a b)
instance Binding a => Binding1 (Untie a)

instance (Irrefutable a, Irrefutable b) => Irrefutable (Untie a b) where
  match (Untie a b) (Untie c d) = match a c <> match b d

instance Irrefutable a => Irrefutable1 (Untie a) where
  match1 f  (Untie a b) (Untie c d) = match a c <> f b d

pi1 :: N k => k (a ∙ b) a
pi1 = nom_ $ \ (Untie a _) -> a

pi2 :: N k => k (a ∙ b) b
pi2 = nom_ $ \ (Untie _ b) -> b

-- this requires a 'fresh', what subset of irrefutable definitions match here?

unit :: (N k, Nominal a, Fresh b) => k a (b ⊸ (a ∙ b))
unit = nom_ $ \ y -> let a = fresh (supp y) in Tie a (Untie y a)

counit :: (N k, Permutable a, Irrefutable b) => k ((b ⊸ a) ∙ b) a
counit = nom_ $ \(Untie (Tie d a) c) -> perm (match c d) a

leftAdjunct :: (N k, Nominal a, Fresh c) => k (a ∙ c) b -> k a (c ⊸ b)
leftAdjunct = nar $ \f y ->
   let a = fresh (supp y)
   in Tie a (f (Untie y a))

rightAdjunct :: (N k, Permutable b, Irrefutable c) => k a (c ⊸ b) -> k (a ∙ c) b
rightAdjunct = nar $ \f (Untie y c) -> case f y of
  Tie d x -> perm (match c d) x

paired :: (NI k, Permutable a) => ((Atom ⊸ a) ∙ Atom) `k` (Atom, a)
paired = niso_ f g where
  f (Untie (Tie a x) a') = (a', trans a' a x)
  g (a, x) = Untie (Tie a x) a
