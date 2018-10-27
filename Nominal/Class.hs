{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}

module Nominal.Class
( Act(..)
, Act1(..)
, Nominal(..)
, (#), support
-- * Generics
, GAct
, GAct1
) where

import Control.Lens hiding (to, from, (#))
import Data.Functor.Contravariant.Generic
import Data.Proxy
import GHC.Generics
import Nominal.Internal.Atom
import Nominal.Internal.Permutation
import Nominal.Internal.Support
import Nominal.Support

class GAct f where
  gact :: Permutation -> f a -> f a

instance Act c => GAct (K1 i c) where
  gact p (K1 a) = K1 (act p a)

instance GAct f => GAct (M1 i c f) where
  gact p (M1 a) = M1 (gact p a)

instance GAct V1 where
  gact _ !v = case v of {}

instance GAct U1 where
  gact _ U1 = U1
  
instance (GAct f, GAct g) => GAct (f :*: g) where
  gact p (a :*: b) = gact p a :*: gact p b

instance (GAct f, GAct g) => GAct (f :+: g) where
  gact p (L1 a) = L1 (gact p a)
  gact p (R1 a) = R1 (gact p a)

instance (Act1 f, GAct g) => GAct (f :.: g) where
  gact p (Comp1 a) = Comp1 (act1 gact p a)

class GAct1 f where
  gact1 :: (Permutation -> a -> a) -> Permutation -> f a -> f a

instance Act c => GAct1 (K1 i c) where
  gact1 _ p (K1 a) = K1 (act p a)

instance GAct1 f => GAct1 (M1 i c f) where
  gact1 f p (M1 a) = M1 (gact1 f p a)

instance GAct1 V1 where
  gact1 _ _ !v = case v of {}

instance GAct1 U1 where
  gact1 _ _ U1 = U1
  
instance (GAct1 f, GAct1 g) => GAct1 (f :*: g) where
  gact1 f p (a :*: b) = gact1 f p a :*: gact1 f p b

instance (GAct1 f, GAct1 g) => GAct1 (f :+: g) where
  gact1 f p (L1 a) = L1 (gact1 f p a)
  gact1 f p (R1 a) = R1 (gact1 f p a)

instance (Act1 f, GAct1 g) => GAct1 (f :.: g) where
  gact1 f p (Comp1 a) = Comp1 (act1 (gact1 f) p a)

instance GAct1 Par1 where
  gact1 f p (Par1 a) = Par1 (f p a)

instance Act1 f => GAct1 (Rec1 f) where
  gact1 f p (Rec1 a) = Rec1 (act1 f p a)

class Act s where
  act :: Permutation -> s -> s
  default act :: (Generic s, GAct (Rep s)) => Permutation -> s -> s
  act p = to . gact p . from

instance Act Atom where 
  act (Permutation t _) (A i) = A (t^.perm i)

instance Act Permutation where
  -- using this action so we can be nominal
  act p t = inv p <> t <> p

class Act1 f where
  act1 :: (Permutation -> s -> s) -> Permutation -> f s -> f s
  default act1 :: (Generic1 f, GAct1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
  act1 f p = to1 . gact1 f p . from1

instance Act1 Proxy
instance Act1 [] 
instance Act1 Maybe

class Act s => Nominal s where
  supp :: s -> Support
  default supp :: Deciding Nominal s => s -> Support
  supp = getSupported $ deciding (Proxy :: Proxy Nominal) (Supported supp)

  -- should this provide how to distribute/collect Tie as well?

instance Nominal Permutation where
  supp (Permutation t0 _) = go t0 where
    go Tip = STip
    go (Bin _ i _ l r) = SBin i (go l) (go r)

instance Nominal Atom where
  supp = singleton

(#) :: Nominal a => Atom -> a -> Bool
a # x = member a (supp x) -- could be more efficient

support :: Nominal a => Supported a
support = Supported supp
