{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Set
( Set
-- * operations
, SetLike(..), (+>), (\/), bottom
-- * fresh variables
, Stream(..), fresh, fresh1
) where

import Control.Lens
import Nominal.Class
import Nominal.Internal.Atom
import qualified Nominal.Internal.Set as Set
import Nominal.Internal.Set (Set(..), depth)

data Stream = !Atom :- Stream deriving Show

-- | Grab an infinite supply of fresh variables relative to a given support.
--
-- This finds an infinite sequence of variables that do not participate in the permutation, placed close to the root
-- the first entry is the 'shallowest' variable id. after that we continue down the tree found until we can produce
-- an infinite family of free variables by using a stride found by the shape of the tree as a 'ray' of variables
-- with some step
fresh :: Set -> Stream
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
fresh1 :: Set -> Atom
fresh1 = freshTree 0 1 where
  freshTree n _ STip = A n
  freshTree n s (SBin d l r)
    | d == 0 = A n
    | dl <= dr = freshTree n' s' l
    | otherwise = freshTree n'' s' r
    where dl=depth l;dr=depth r;n'=n+s;n''=n'+s;s'=s+s;

-- not known at the right point

-- (<>) = union, mempty = bottom
class (Index a ~ Atom, Contains a, NominalMonoid a) => SetLike a where
  insert :: Atom -> a -> a
  insert a = contains a .~ True
  {-# inline insert #-}

  delete :: Atom -> a -> a
  delete a = contains a .~ False
  {-# inline delete #-}

  member :: Atom -> a -> Bool
  member = view . contains
  {-# inline member #-}

  singleton :: Atom -> a
  singleton a = insert a mempty
  {-# inline singleton #-}

  (/\) :: a -> a -> a

  (\\) :: a -> a -> a
  p \\ q = p /\ xor p q
  {-# inline (\\) #-}

  xor :: a -> a -> a
  xor p q = (p \\ q) \/ (q \\ p)
  {-# inline xor #-}
  {-# minimal (/\), (xor | (\\)) #-}

infixr 7 /\
infixr 6 +>
infixr 5 \/

(+>) :: SetLike a => Atom -> a -> a
(+>) = insert

(\/) :: SetLike a => a -> a -> a
(\/) = (<>)

bottom :: SetLike a => a
bottom = mempty 

instance SetLike Set where
  insert = Set.insert
  delete = Set.delete
  member = Set.member
  singleton = Set.singleton
  (/\) = Set.intersect
  (\\) = Set.diff
  xor = Set.xor
