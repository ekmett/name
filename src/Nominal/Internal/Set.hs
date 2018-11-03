{-# language LambdaCase #-}
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

module Nominal.Internal.Set
( Set(..)
, member, insert, delete
, diff, union, intersect, singleton, xor
, intersects
, depth
) where

import Control.Lens
import Data.Semigroup hiding (diff)
import Nominal.Internal.Trie (Atom(..))

-- the int is the depth of the shallowest free variable
-- when it is 0, this element is free. invariant:
-- SBin 0 Tip Tip is forbidden
data Set = STip | SBin !Int !Set !Set
  deriving Eq

depth :: Set -> Int
depth STip = 0
depth (SBin i _ _) = i

sbin :: Bool -> Set -> Set -> Set
sbin False STip STip = STip
sbin t l r  = SBin (if t then depth l + depth r + 1 else 0) l r

union :: Set -> Set -> Set
union STip a = a
union a STip = a
union (SBin i li ri) (SBin j lj rj) = sbin (i /= 0 && j /= 0) (union li lj) (union ri rj)

instance Semigroup Set where
  (<>) = union
  stimes = stimesIdempotentMonoid

instance Monoid Set where
  mempty = STip

xor :: Set -> Set -> Set
xor STip a = a
xor a STip = a
xor (SBin i li ri) (SBin j lj rj)
  = sbin ((i==0)/=(j==0)) (xor li lj) (xor ri rj)

intersect :: Set -> Set -> Set
intersect STip _ = STip
intersect _ STip = STip
intersect (SBin i li ri) (SBin j lj rj) = sbin (i /= 0 && j /= 0) (intersect li lj) (intersect ri rj)

-- check overlap, rather than construct a whole set
intersects :: Set -> Set -> Bool
intersects STip _ = False
intersects _ STip = False
intersects (SBin i li ri) (SBin j lj rj) = min i j > 0 || intersects li lj || intersects ri rj

diff :: Set -> Set -> Set
diff a STip = a
diff STip _ = STip
diff (SBin i li ri) (SBin j lj rj) = sbin (i == 0 && j /= 0) (diff li lj) (diff ri rj)

member :: Atom -> Set -> Bool
member (A i0) = go i0 where
  go _ STip = False
  go 0 (SBin i _ _) = i == 0
  go k (SBin _ l r) = case (k - 1) `divMod` 2 of
    (q,0) -> go q l
    (q,_) -> go q r

delete :: Atom -> Set -> Set
delete (A i0) = go i0 where
  go _ STip = STip
  go 0 (SBin _ l r) = sbin False l r
  go k (SBin i l r) = case (k - 1) `divMod` 2 of
    (q,0) -> sbin (i/=0) (go q l) r
    (q,_) -> sbin (i/=0) l (go q r)

insert :: Atom -> Set -> Set
insert (A i0) = go i0 where
  go k STip = singleton (A k)
  go 0 (SBin _ l r) = sbin True l r
  go k (SBin i l r) = case (k - 1) `divMod` 2 of
    (q,0) -> sbin (i/=0) (go q l) r
    (q,_) -> sbin (i/=0) l (go q r)

singleton :: Atom -> Set
singleton (A k0) = go k0 where
  go 0 = SBin 0 STip STip
  go k = case (k-1) `divMod` 2 of
    (q,0) -> sbin False (go q) STip
    (q,_) -> sbin False STip (go q)

-- lens classes
type instance Index Set = Atom
instance Contains Set where
  contains (A i0) = go i0 where
    go k f STip = f False <&> \t -> if t then singleton (A k) else STip
    go 0 f (SBin i l r) = f (i/=0) <&> \t -> sbin t l r
    go k f (SBin i l r) = case (k - 1) `divMod` 2 of
      (q,0) -> go q f l <&> \ l' -> sbin (i/=0) l' r
      (q,_) -> go q f r <&> \ r' -> sbin (i/=0) l r'

instance AsEmpty Set where
  _Empty = prism (const STip) $ \case
    STip -> Right ()
    t    -> Left t
