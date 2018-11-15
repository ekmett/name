{-# Language GADTs #-}
{-# Language ViewPatterns #-}
{-# Language FlexibleContexts #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language LambdaCase #-}
{-# Language DeriveGeneric #-}
{-# Language DeriveAnyClass #-}
{-# Language TupleSections #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- Support is, effectively, a vocabulary for talking about stabilizers.
--
-- @G(x) = { y ∈ X | y = g.x, g ∈ G }@ is the orbit of @x ∈ X@ under @G@.
--
-- @G_x = { g ∈ G | g.x = x }@ is the stabilizer of @x@ in G.
--
-- @G(x) = G/G_x@ and the group's action on @G_x@ is transitive.
--
-- Classically (no pun intended) minimal support is computable. In practice, for computer science needs a finite superset of support
-- suffices, but at the cost of transitivity.
--
-- We normally (no pun intended) talk about support in terms of sets of atoms that if you hold them in place, πx=x.
--
-- It seems to me that this isn't the right notion!
--
-- Consider centralizers and normalizers,
--
-- @C_G(A) = { g ∈ G | ∀a ∈ A, gag⁻¹=a }@ is the centralizer of @A@ in @G@
--
-- @N_G(A) = { g ∈ G | gA = Ag }@ is the normalizer of @A@ in @G@
--
-- @C_G(A) ⊆ N_G(A) ⊆ G@
--
-- All of the literature on nominal sets I can find actually only talks about support, which speaks to stabilizers, to get at centralizers.
--
-- In general, this seems to make sense, for single atoms, @C_G(a) = N_G(a)@!
--
-- But consider sets of atoms, not to be confused by the sets in the category Set which are being acted on by permutations in Nom.
-- e.g. the @Set@ type in @Nominal.Set@. Those are stable under the larger class @N_G(A)@. You can permute elements in their support,
-- you can permute elements outside of their support, but don't cross the boundary in any cycle.
--
-- Properly talking about their support for these is effectively talking about partitions that we'd have to respect on atoms. Properly
-- computing minimal support here should be computing @N_G(S)@ for the set S of atoms they cover, not @C_G(S)@.
--
-- In math terms, Sym(K)*Sym(N-K) is not just a subgroup of Sym(N), it is a maximal subgroup. These aren't the only maximal subgroups of
-- Sym(N), but I can't think of any particular use for the wreath product subgroups at this time!
--
-- We currently don't store sets of variables very often in terms and the like, but I'd like to be able to reason about things more clearly here
-- so I'll "wear the hair shirt" and pay for the more complicted representation.
--
-- I'm using @discrimination@ to deal with collecting the partitions.
--
---------------------------------------------------------------------------------

module Data.Name.Support where

import Control.Lens hiding (set, sets)
import Data.Discrimination.Grouping
import qualified Data.List as List
import Data.Name.Lattice
import Data.Name.Internal.Trie as Trie
import Data.Name.Set as Set
import Data.Void
import qualified GHC.Exts as Exts
import GHC.Generics

data Support where
  Supp :: (Eq a, Grouping a) => Trie a -> Support

instance Show Support where
  showsPrec d xs = showParen (d > 10) $
     showString "Supp " . showsPrec 11 (partitions xs)

-- | The finest support compatible with this support
-- this is a local top
finest :: Support -> Support
finest (Supp xs) = Supp (imap const xs)

-- | Fixing N elements, this is the local coarsest partition.
--
-- @coarsest . supp = id :: Set -> Set@
coarsest :: Support -> Set
coarsest (Supp xs) = Set xs

sets :: Support -> [Set]
sets (Supp t) = Exts.fromList <$> runGroup grouping (ifoldr (\i a r -> (a, i): r) [] t)

unsets :: [Set] -> Support
unsets = Supp . ifoldr (\i (Set t) r -> Trie.union (i <$ t) r) Empty

-- | Meets compute coarser supports by glomming together partitions
instance Meet Support where
  xs0 ∧ ys0 = unsets $ go (sets xs0) (sets ys0) where
    go _ [] = []
    go [] ys = ys
    go (x:xs) ys = go1 x xs ys
    go1 x xs ys = case List.partition (Set.disjoint x) ys of
      (_, []) -> x : go xs ys
      (ys', Prelude.foldr (∨) x -> x') -> go1 x' ys' xs

data These a b = This a | That b | These a b deriving (Generic, Eq, Ord, Show, Grouping)

-- | Joins compute finer grained supports on a set of elements
instance Join Support where
  Supp xs ∨ Supp ys = Supp $ imerge (\_ x y -> Just $ These x y) (fmap This) (fmap That) xs ys

instance BoundedJoin Support where
  bottom = Supp (Empty :: Trie Void)

instance Semigroup Support where
  (<>) = (∨)

instance Monoid Support where
  mempty = bottom

flop :: a -> b -> [(b,a)] -> [(b,a)]
flop k v r = (v,k):r

canonical :: Support -> [[Name]]
canonical (Supp xs) = runGroup grouping $ ifoldr flop [] xs

partitions :: Support -> [Set]
partitions = fmap (Set . Trie.fromDistinctAscList . fmap (,())) . canonical

instance PartialOrder Support where
  -- |
  -- @
  -- {{x,y},U-{x,y}} ⊆ {{x,y},{z},U-{x,y,z}}
  -- {{x,y},U-{x,y}} ⊆ {{x},{y},U-{x,y}}
  -- @
  Supp ys ⊆ Supp xs
      = null (diff ys xs) -- @{{x,y},U-{x,y}} is not ⊆ {{x},U-{x}}@
     && all similar (runGroup grouping $ ifoldr flop [] xs) where -- ensure every partition of xs is a subpartition of a partition of ys
    similar zs = all (\ p -> z == ys^.at p) zs where
      z = ys^.at (head zs)

-- TODO: compute this more productively using the guts of 'Grouping'
instance Eq Support where
  xs == ys = canonical xs == canonical ys

sans :: Support -> Set -> Support
sans (Supp xs) (Set ys) = Supp (Trie.diff xs ys)
