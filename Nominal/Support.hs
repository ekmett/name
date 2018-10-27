{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}

module Nominal.Support
( Supported(..)
, Support
, member
, contains
, pattern Empty
, delete, insert, diff, union, intersect, singleton
-- fresh variables
, Stream(..), fresh, fresh1
) where

import Control.Lens
import Data.Functor.Contravariant.Divisible
import Data.Void
import Nominal.Internal.Atom
import Nominal.Internal.Support

newtype Supported a = Supported { getSupported :: a -> Support }

instance Contravariant Supported where
  contramap f (Supported g) = Supported (g . f)

instance Divisible Supported where
  conquer = Supported $ \_ -> mempty
  divide f (Supported g) (Supported h) = Supported $ \a -> case f a of
    (b, c) -> g b <> h c

instance Decidable Supported where
  lose f = Supported $ absurd . f 
  choose f (Supported g) (Supported h) = Supported $ \a -> case f a of
    Left b -> g b
    Right c -> h c 

data Stream = !Atom :- Stream deriving Show

-- | Grab an infinite supply of fresh variables relative to a given support.
--
-- This finds an infinite sequence of variables that do not participate in the permutation, placed close to the root
-- the first entry is the 'shallowest' variable id. after that we continue down the tree found until we can produce
-- an infinite family of free variables by using a stride found by the shape of the tree as a 'ray' of variables
-- with some step
fresh :: Support -> Stream
fresh = freshTree 0 1 where
  fill !n !s = A n :- fill (n + s) s
  freshTree n s STip = fill n s
  freshTree n s (SBin d l r)
    | dl <= dr = tweak (freshTree n' s' l)
    | otherwise = tweak (freshTree n'' s' r)
    where dl=depth l;dr=depth r;n'=n+s;n''=n'+s;s'=s+s;
           -- grab opportunistic fresh variables near the root on the way down
          tweak | d == 0 = (A n :-)
                | otherwise = id

-- | Grab a single fresh variable relative to a given support
fresh1 :: Support -> Atom
fresh1 = freshTree 0 1 where
  freshTree n _ STip = A n
  freshTree n s (SBin d l r)
    | d == 0 = A n
    | dl <= dr = freshTree n' s' l
    | otherwise = freshTree n'' s' r
    where dl=depth l;dr=depth r;n'=n+s;n''=n'+s;s'=s+s;

