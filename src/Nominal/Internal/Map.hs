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

module Nominal.Internal.Map where

import Control.Category ((>>>))
import Control.Lens
import Data.Functor.Compose
import Nominal.Class
import Nominal.Internal.Trie (Atom(..))
import Nominal.Internal.Set (Set(..))
import Nominal.Set ((+>))
import Numeric.Natural

-- maps from atoms to values, contains a memoized approximate support
data Map a = Map !Set !(Tree a)

data Tree a
  = Tip 
  | Bin a !(Tree a) !(Tree a)
  | Bin_  !(Tree a) !(Tree a)

bin :: Maybe a -> Tree a -> Tree a -> Tree a
bin Nothing Tip Tip = Tip
bin Nothing l r = Bin_ l r
bin (Just a) l r = Bin a l r
{-# inline bin #-}

bin_ :: Tree a -> Tree a -> Tree a
bin_ Tip Tip = Tip
bin_ l r = Bin_ l r
{-# inline bin_ #-}

-- nominal
union :: NominalSemigroup a => Map a -> Map a -> Map a
union (Map s0a t0a) (Map s0b t0b) = Map (s0a <> s0b) (go t0a t0b) where
  go Tip a = a
  go a Tip = a
  go (Bin i li ri) (Bin j lj rj) = Bin (i <> j) (go li lj) (go ri rj)
  go (Bin i li ri) (Bin_ lj rj)  = Bin i (go li lj) (go ri rj)
  go (Bin_ li ri)  (Bin j lj rj) = Bin j (go li lj) (go ri rj)
  go (Bin_ li ri)  (Bin_ lj rj)  = Bin_ (go li lj) (go ri rj)

instance NominalSemigroup a => Semigroup (Map a) where
  (<>) = union

instance NominalSemigroup a => Monoid (Map a) where
  mempty = Map mempty Tip

instance NominalSemigroup a => NominalSemigroup (Map a)
instance NominalSemigroup a => NominalMonoid (Map a)

-- requires a nominal morphism, if so, nominal
intersectWith :: (a -> b -> c) -> Map a -> Map b -> Map c
intersectWith f (Map s0 t0) (Map s1 t1) = tweak $ go t0 t1 where
  tweak Tip = Map mempty Tip -- force us back to mempty if we're empty
  tweak t = Map (s0 <> s1) t
  go Tip _ = Tip
  go _ Tip = Tip
  go (Bin i li ri) (Bin j lj rj) = Bin (f i j) (go li lj) (go ri rj)
  go (Bin_  li ri) (Bin _ lj rj) = bin_ (go li lj) (go ri rj)
  go (Bin _ li ri) (Bin_ lj rj)  = bin_ (go li lj) (go ri rj)
  go (Bin_  li ri) (Bin_ lj rj)  = bin_ (go li lj) (go ri rj)
  
-- nominal
intersect :: Map a -> Map a -> Map a
intersect (Map s0 t0) (Map _ t1) = tweak $ go t0 t1 where
  tweak Tip = Map mempty Tip -- force us back to mempty if we're empty
  tweak t = Map s0 t -- all entries exist in the left tree
  go Tip _ = Tip
  go _ Tip = Tip
  go (Bin i li ri) (Bin _ lj rj) = Bin i (go li lj) (go ri rj)
  go (Bin_  li ri) (Bin _ lj rj) = bin_ (go li lj) (go ri rj)
  go (Bin _ li ri) (Bin_  lj rj) = bin_ (go li lj) (go ri rj)
  go (Bin_  li ri) (Bin_  lj rj) = bin_ (go li lj) (go ri rj)
  
-- nominal
diff :: Map a -> Set -> Map a
diff (Map s0 t0) = tweak . go t0 where
  tweak Tip = Map mempty Tip
  tweak t = Map s0 t
  go a STip = a
  go Tip _ = Tip
  go (Bin _ li ri) (SBin 0 lj rj) = bin_ (go li lj) (go ri rj)
  go (Bin a li ri) (SBin _ lj rj) = bin (Just a) (go li lj) (go ri rj)
  go (Bin_ li ri)  (SBin _ lj rj) = bin_ (go li lj) (go ri rj)

-- nominal
(\\) :: Map a -> Set -> Map a
(\\) = diff

-- nominal
lookup :: Atom -> Map a -> Maybe a
lookup (A i0) (Map _ t0) = go i0 t0 where
  go _ Tip = Nothing
  go 0 (Bin i _ _) = Just i
  go 0 (Bin_ _ _) = Nothing
  go k (Bin _ l r) = case (k-1) `divMod` 2 of
    (q,0) -> go q l
    (q,_) -> go q r
  go k (Bin_ l r) = case (k-1) `divMod` 2 of
    (q,0) -> go q l
    (q,_) -> go q r

-- nominal
delete :: Atom -> Map a -> Map a
delete (A i0) (Map s0 t0) = tweak $ go i0 t0 where
  tweak Tip = Map mempty Tip
  tweak t = Map s0 t
  go _ Tip = Tip
  go 0 (Bin _ l r) = bin_ l r
  go k (Bin i l r) = case (k - 1) `divMod` 2 of
    (q,0) -> Bin i (go q l) r
    (q,_) -> Bin i l (go q r)
  go 0 (Bin_ l r) = bin_ l r
  go k (Bin_ l r) = case (k - 1) `divMod` 2 of
    (q,0) -> bin_ (go q l) r
    (q,_) -> bin_ l (go q r)

-- nominal
insert :: Nominal a => Atom -> a -> Map a -> Map a
insert v@(A i0) a0 (Map s0 t0) = Map (v +> supp a0 <> s0) $ go i0 a0 t0 where
  go k a Tip = singletonTree k a
  go 0 a (Bin_ l r) = Bin a l r
  go k a (Bin_ l r) = case (k - 1) `divMod` 2 of
    (q,0) -> bin_ (go q a l) r
    (q,_) -> bin_ l (go q a r)
  go 0 a (Bin _ l r) = Bin a l r
  go k a (Bin i l r) = case (k - 1) `divMod` 2 of
    (q,0) -> bin (Just i) (go q a l) r
    (q,_) -> bin (Just i) l (go q a r)

-- nominal
singleton :: Nominal a => Atom -> a -> Map a
singleton v@(A k0) a = Map (v +> supp a) (singletonTree k0 a)

singletonTree :: Natural -> a -> Tree a
singletonTree 0 a = Bin a Tip Tip
singletonTree k a = case (k-1) `divMod` 2 of
    (q,0) -> Bin_ (singletonTree q a) Tip
    (q,_) -> Bin_ Tip (singletonTree q a)
  
-- lens classes
type instance Index (Tree a) = Atom
type instance IxValue (Tree a) = a
instance Ixed (Tree a)
instance At (Tree a) where
  at (A i0) = go i0 where
    go k f Tip = f Nothing <&> \case
      Nothing -> Tip
      Just a -> singletonTree k a
    go 0 f (Bin i l r) = f (Just i) <&> \t -> bin t l r
    go k f (Bin i l r) = case (k - 1) `divMod` 2 of
      (q,0) -> go q f l <&> \ l' -> Bin i l' r
      (q,_) -> go q f r <&> \ r' -> Bin i l r'
    go 0 f (Bin_ l r) = f Nothing <&> \t -> bin t l r
    go k f (Bin_ l r) = case (k - 1) `divMod` 2 of
      (q,0) -> go q f l <&> \ l' -> bin_ l' r
      (q,_) -> go q f r <&> \ r' -> bin_ l r'

type instance Index (Map a) = Atom
type instance IxValue (Map a) = a
instance Nominal a => Ixed (Map a)
instance Nominal a => At (Map a) where
  -- at :: Functor f => Atom -> (Maybe a -> f (Maybe a)) -> Map a -> f (Map a)
  at a0 f0 (Map s0 t0) = tweak <$> getCompose (at a0 (Compose . fmap diag . f0) t0) where
    diag a = (a,a)
    tweak (_, Tip)    = Map mempty Tip
    tweak (Just a,t)  = Map (a0 +> supp a <> s0) t
    tweak (Nothing,t) = Map s0 t

instance AsEmpty (Map a) where
  _Empty = prism (const (Map mempty Tip)) $ \case
    Map _ Tip -> Right ()
    t         -> Left t

instance Perm1 Tree where
  -- TODO: adapt Perm Set
  perm1 f0 p0 t0 = go f0 0 1 p0 t0 Tip where
    go _ _ _ _ Tip = id
    go f n s p (Bin_ l r)
        = go f n' s' p l
      >>> go f n'' s' p r
      where n'=n+s;s'=s+s;n''=n'+s
    go f n s p (Bin x l r)
        = at (perm p (A n)) ?~ f p x 
      >>> go f n' s' p l
      >>> go f n'' s' p r
      where n'=n+s;s'=s+s;n''=n'+s

instance Perm a => Perm (Tree a) where
  -- TODO: use my Perm Set approach, this makes it cheaper for small permutations
  -- or small maps
  perm p0 t0 = go 0 1 p0 t0 Tip where
    go _ _ _ Tip = id
    go n s p (Bin_ l r)
        = go n' s' p l
      >>> go n'' s' p r
      where n'=n+s;s'=s+s;n''=n'+s
    go n s p (Bin x l r)
        = at (perm p (A n)) ?~ perm p x 
      >>> go n' s' p l
      >>> go n'' s' p r
      where n'=n+s;s'=s+s;n''=n'+s

instance Nominal a => Nominal (Tree a) where
  supp = go 0 1 where
    go _ _ Tip = mempty
    go n s (Bin_ l r) = go n' s' l <> go n'' s' r
      where n'=n+s;s'=s+s;n''=n'+s
    go n s (Bin a l r) = A n +> supp a <> go n' s' l <> go n'' s' r
      where n'=n+s;s'=s+s;n''=n'+s
    
-- nominal, clean up the cached support
trim :: Nominal a => Map a -> Map a
trim (Map _ t0) = Map (supp t0) t0

instance Perm1 Map where
  perm1 f p (Map s t) = Map (perm p s) (perm1 f p t)

-- good at small permutations, like the ones produced by swaps
instance Perm a => Perm (Map a) where
  perm p (Map s t) = Map (perm p s) (perm p t)

-- uses memoization, so weaker condition than I'd otherwise expect
instance Perm a => Nominal (Map a) where
  supp (Map s _) = s

