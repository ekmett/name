---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Supported where

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Void
import Nominal.Support
import Nominal.Lattice

newtype Supported a = Supported { getSupported :: a -> Support }

instance Contravariant Supported where
  contramap f (Supported g) = Supported (g . f)

instance Divisible Supported where
  conquer = Supported $ \_ -> top
  divide f (Supported g) (Supported h) = Supported $ \a -> case f a of
    (b, c) -> g b ∧ h c

instance Decidable Supported where
  lose f = Supported $ absurd . f
  choose f (Supported g) (Supported h) = Supported $ \a -> case f a of
    Left b -> g b
    Right c -> h c
