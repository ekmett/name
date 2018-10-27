{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}

module Nominal.Internal.Set
( Set(..)
, member
, contains
, pattern Empty
, delete, insert, diff, union, intersect, singleton
, (\\)
, depth -- debugging
) where

import Control.Lens
import Nominal.Internal.Atom

data Set = STip | SBin !Int !Set !Set -- int is the depth of the shallowest free variable 

depth :: Set -> Int
depth STip = 0
depth (SBin i _ _) = i

sbin :: Bool -> Set -> Set -> Set
sbin False STip STip = STip
sbin t l r  = SBin (if t then 0 else depth l + depth r + 1) l r

union :: Set -> Set -> Set
union STip a = a
union a STip = a
union (SBin i li ri) (SBin j lj rj) = sbin (i == 0 || j == 0) (union li lj) (union ri rj)

instance Semigroup Set where
  (<>) = union

instance Monoid Set where
  mempty = STip

intersect :: Set -> Set -> Set
intersect STip _ = STip
intersect _ STip = STip
intersect (SBin i li ri) (SBin j lj rj) = sbin (i == 0 && j == 0) (intersect li lj) (intersect ri rj)

diff :: Set -> Set -> Set
diff a STip = a
diff STip _ = STip
diff (SBin i li ri) (SBin j lj rj) = sbin (i == 0 && j /= 0) (diff li lj) (diff ri rj)

(\\) :: Set -> Set -> Set
(\\) = diff

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
    (q,0) -> sbin (i == 0) (go q l) r
    (q,_) -> sbin (i == 0) l (go q r)

insert :: Atom -> Set -> Set
insert (A i0) = go i0 where
  go k STip = singleton (A k)
  go 0 (SBin _ l r) = sbin True l r
  go k (SBin i l r) = case (k - 1) `divMod` 2 of
    (q,0) -> sbin (i == 0) (go q l) r
    (q,_) -> sbin (i == 0) l (go q r)

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
    go 0 f (SBin i l r) = f (i == 0) <&> \t -> sbin t l r
    go k f (SBin i l r) = case (k - 1) `divMod` 2 of
      (q,0) -> go q f l <&> \ l' -> sbin (i == 0) l' r
      (q,_) -> go q f r <&> \ r' -> sbin (i == 0) l r'

instance AsEmpty Set where
  _Empty = prism (const STip) $ \case
    STip -> Right ()
    t    -> Left t
