{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language DeriveGeneric #-}
{-# language MonoLocalBinds #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Class
( Permutable(..), Permutable1(..)
, Nominal(..), Nominal1(..)
, Supply(..), suppgen, equivgen, sepgen, supplysupp, supplygen
, Fresh(..), Fresh1(..), fresh
-- , (#), support
, NominalSemigroup, NominalMonoid
-- * Generics
, GPermutable, GPermutable1, transgen, permgen
-- * Binding
, Binding(..), Binding1(..)
, Irrefutable(..), Irrefutable1(..)
-- * Internals
, Supported(..)
, Binder(..)
) where

import Control.Monad
import Control.Lens hiding (to, from, (#))
import Data.Coerce
import Data.Discrimination.Grouping
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant.Generic
import qualified Data.Map.Internal as Map
import Data.Name.Type
import Data.Name.Internal.Trie as Trie
import Data.Name.Internal.Permutation
import Data.Name.Set as Set
import Data.Name.Permutation
import Data.Name.Support
import Data.Name.Logic
import Data.Proxy
import Data.Void
import GHC.Generics
import Prelude hiding (elem)

--------------------------------------------------------------------------------
-- * Permutable
--------------------------------------------------------------------------------

transgen :: (Generic s, GPermutable (Rep s)) => Name -> Name -> s -> s
transgen i j = to . gtrans i j . from
{-# inline [0] transgen #-}

permgen :: (Generic s, GPermutable (Rep s)) => Permutation -> s -> s
permgen p = to . gperm p . from
{-# inline [0] permgen #-}

{-# RULES
"transgen/transgen/ijij" [~1] forall i j x. transgen i j (transgen i j x) = x
"transgen/transgen/ijji" [~1] forall i j x. transgen i j (transgen j i x) = x
"permgen/swap=transgen" [~1] forall i j. permgen (swap i j) = transgen i j
"permgen/mempty=id" [~1] forall x. permgen (Permutation (Tree (Trie Map.Tip)) x) = id
  #-}

class Permutable s where
  trans :: Name -> Name -> s -> s
  default trans :: (Generic s, GPermutable (Rep s)) => Name -> Name -> s -> s
  trans = transgen
  {-# inline trans #-}

  -- |
  -- @
  -- perm mempty = id
  -- perm (p <> q) = perm p . perm q
  -- @
  perm :: Permutation -> s -> s
  default perm :: (Generic s, GPermutable (Rep s)) => Permutation -> s -> s
  perm = permgen
  {-# inline perm #-}

instance Permutable Name where
  trans a b c
    | c == a = b
    | c == b = a
    | otherwise = c
  {-# inline trans #-}
  perm (Permutation t _) i = permTree t i
  {-# inline perm #-}

instance Permutable Permutation where
  trans a b t = swap a b <> t <> swap a b
  {-# inline trans #-}
  perm p t = p <> t <> inv p
  {-# inline perm #-}

instance Permutable Set where
  trans i j s = s
    & contains j .~ s^.contains i
    & contains i .~ s^.contains j
  {-# inline trans #-}
  perm (Permutation (Tree p) _) z = ifoldr tweak z p where
    tweak i j s = s & contains j .~ z^.contains i -- can't use trans, note s /= z
  {-# inline perm #-}

instance Permutable Support where
  trans i j (Supp s) = Supp $ s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm (Permutation (Tree p) _) (Supp z) = Supp $ ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
  {-# inline perm #-}

instance Permutable a => Permutable (Trie a) where
  trans i j s = s
    & at j .~ s^.at i
    & at i .~ s^.at j
  {-# inline trans #-}
  perm p0@(Permutation (Tree p) _) t = ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
    z = perm p0 <$> t
  {-# inline perm #-}

instance (Permutable a, Permutable b) => Permutable (a -> b) where
  trans a b f = trans a b . f . trans a b
  {-# inline trans #-}
  perm p f = perm p . f . perm (inv p)
  {-# inline perm #-}

instance Permutable Prop
instance (Permutable a, Permutable b) => Permutable (a, b)
instance (Permutable a, Permutable b, Permutable c) => Permutable (a, b, c)
instance (Permutable a, Permutable b, Permutable c, Permutable d) => Permutable (a, b, c, d)
instance (Permutable a, Permutable b) => Permutable (Either a b)
instance Permutable a => Permutable [a]
instance Permutable a => Permutable (Maybe a)
instance Permutable (Proxy a)
instance Permutable Void
instance Permutable ()
instance Permutable Bool
instance Permutable Char where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}
instance Permutable Int where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}
instance Permutable Word where
  trans _ _ = id
  {-# inline trans #-}
  perm _ = id
  {-# inline perm #-}

--------------------------------------------------------------------------------
-- * Permutable1
--------------------------------------------------------------------------------

transgen1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Name -> Name -> s -> s) -> Name -> Name -> f s -> f s
transgen1 f a b = to1 . gtrans1 f a b . from1
{-# inline [0] transgen1 #-}

permgen1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
permgen1 f p = to1 . gperm1 f p . from1
{-# inline [0] permgen1 #-}

{-# RULES
"transgen1/transgen1/ijij" [~1] forall f i j x. transgen1 f i j (transgen1 f i j x) = x
"transgen1/transgen1/ijji" [~1] forall f i j x. transgen1 f i j (transgen1 f j i x) = x
"permgen1/swap=transgen1" [~1] forall f i j. permgen1 f (swap i j) = transgen1 (\x y -> f (swap x y)) i j
"permgen1/mempty=id" [~1] forall f x. permgen1 f (Permutation (Tree (Trie Map.Tip)) x) = id
  #-}

class Permutable1 f where
  trans1 :: (Name -> Name -> s -> s) -> Name -> Name -> f s -> f s
  default trans1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Name -> Name -> s -> s) -> Name -> Name -> f s -> f s
  trans1 = transgen1
  {-# inline trans1 #-}

  perm1 :: (Permutation -> s -> s) -> Permutation -> f s -> f s
  default perm1 :: (Generic1 f, GPermutable1 (Rep1 f)) => (Permutation -> s -> s) -> Permutation -> f s -> f s
  perm1 = permgen1
  {-# inline perm1 #-}

instance Permutable1 Proxy
instance Permutable1 []
instance Permutable1 Maybe
instance Permutable a => Permutable1 ((,)a)
instance (Permutable a, Permutable b) => Permutable1 ((,,) a b)
instance (Permutable a, Permutable b, Permutable c) => Permutable1 ((,,,) a b c)
instance Permutable a => Permutable1 (Either a)

instance Permutable1 Trie where
  trans1 f i j s = z
    & at j .~ z^.at i
    & at i .~ z^.at j
    where z = f i j <$> s
  {-# inline trans1 #-}
  perm1 f p0@(Permutation (Tree p) _) t = ifoldr tweak z p where
    tweak i j s = s & at j .~ z^.at i
    z = f p0 <$> t
  {-# inline perm1 #-}

--------------------------------------------------------------------------------
-- * Supplys
--------------------------------------------------------------------------------

newtype Supply = Supply {getSupply :: Name} deriving Generic

instance Semigroup Supply where
  Supply a <> Supply b = Supply (max a b)

instance Monoid Supply where
  mempty = Supply 0

{-
instance Permutable Supply where
  trans i j (a :- as) = trans i j a :- trans i j as
  perm p (a :- as) = perm p a :- perm p as
-}

--------------------------------------------------------------------------------
-- * Supported
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- * Nominal
--------------------------------------------------------------------------------

sepgen :: Deciding Nominal s => Name -> s -> Bool
sepgen a = getPredicate $ deciding (Proxy :: Proxy Nominal) (Predicate (a #))
{-# inline sepgen #-}

suppgen :: Deciding Nominal s => s -> Support
suppgen = getSupported $ deciding (Proxy :: Proxy Nominal) (Supported supp)
{-# inline suppgen #-}

equivgen :: Deciding Nominal s => s -> Name -> Name -> Bool
equivgen s i j = getPredicate (deciding (Proxy :: Proxy Nominal) (Predicate (\s' -> equiv s' i j))) s
{-# inline equivgen #-}

supplygen :: Deciding Nominal s => s -> Supply
supplygen = getOp $ deciding (Proxy :: Proxy Nominal) (Op supply)

-- fast if you have O(1) support
supplysupp :: Nominal s => s -> Supply
supplysupp (supp -> Supp s) = Supply $ maybe (Name 0) (1+) $ sup s

class Permutable s => Nominal s where

  -- @
  -- a # x = not (member a (supp b))
  -- @
  (#) :: Name -> s -> Bool
  default (#) :: Deciding Nominal s => Name -> s -> Bool
  (#) = sepgen
  {-# inline (#) #-}
  -- | The usual convention in nominal sets is to say something like:
  --
  -- @
  -- if (forall x in supp s. perm p x = x) then perm p s = s
  -- @
  --
  -- here,
  --
  -- @
  -- if (forall x in supp s. equiv (supp s) (perm p x) x) then perm p s = s
  -- @
  --
  -- This enables supports to describe allowed permutations.
  --
  -- Consider, a set of atoms, membership will return true given any atom in the set.
  -- but if you permuted those atoms that are within the set amongst themselves
  -- the answer wouldn't change. Similarly if you permuted elements that are solely
  -- outside of the set, the answer wouldn't change. It is only when you permute in
  -- such a way that exchanges elements from within the set with elements outside of
  -- the set that the answer fails to match
  supp :: s -> Support
  default supp :: Deciding Nominal s => s -> Support
  supp = suppgen
  {-# inline supp #-}

  supply :: s -> Supply
  default supply :: Deciding Nominal s => s -> Supply
  supply = supplygen
  {-# inline supply #-}

  -- equivalent modulo support
  equiv :: s -> Name -> Name -> Bool
  default equiv :: Deciding Nominal s => s -> Name -> Name -> Bool
  equiv = equivgen
  {-# inline equiv #-}

instance Nominal Permutation where
  a # Permutation (Tree t) _ = not (Trie.member a t)
  supp (Permutation (Tree t) _) = Supp t
  supply = supplysupp
  equiv = equiv . supp

instance Nominal Support where
  a # Supp s = not (Trie.member a s)
  supp = id
  supply = supplysupp
  equiv (Supp s) i j = s^.at i == s^.at j

instance Nominal Name where
  equiv a b c = (a == b) == (a == c)
  supply (Name i) = Supply $ Name (i+1)
  (#) = (/=)
  supp a = Supp (Trie.singleton a ())

newtype Blind a = Blind a
instance Eq (Blind a) where _ == _ = True
instance Ord (Blind a) where compare _ _ = EQ
instance Grouping (Blind a) where grouping = conquer

instance Nominal Set where
  a # s = not (Set.member a s)
  supply = supplysupp
  supp (Set s) = Supp (go s) where
    go :: Trie a -> Trie (Blind a)
    go = coerce
    _ignore :: a -> Blind a
    _ignore = Blind

  equiv s i j = Set.member i s == Set.member j s

instance (Nominal a, Nominal b) => Nominal (a, b)
instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c)
instance (Nominal a, Nominal b, Nominal c, Nominal d) => Nominal (a, b, c, d)
instance (Nominal a, Nominal b) => Nominal (Either a b)
instance Nominal a => Nominal [a]
instance Nominal a => Nominal (Maybe a)
instance Nominal (Proxy a)
instance Nominal Void where
  equiv = absurd
  supply = absurd
  supp  = absurd
  (#) _ = absurd

instance Nominal ()

instance Nominal Bool where
  equiv _ _ _ = True

instance Nominal Int where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

instance Nominal Char where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

instance Nominal Word where
  equiv _ _ _ = True
  _ # _ = True
  supp _ = mempty
  supply _ = mempty

--------------------------------------------------------------------------------
-- * Lifted Nominal Support
--------------------------------------------------------------------------------

supp1gen :: Deciding1 Nominal f => (s -> Support) -> f s -> Support
supp1gen f = getSupported $ deciding1 (Proxy :: Proxy Nominal) (Supported supp) (Supported f)

supply1gen :: Deciding1 Nominal f => (s -> Supply) -> f s -> Supply
supply1gen f = getOp $ deciding1 (Proxy :: Proxy Nominal) (Op supply) (Op f)

class Permutable1 f => Nominal1 f where
  supp1 :: (s -> Support) -> f s -> Support
  default supp1 :: Deciding1 Nominal f => (s -> Support) -> f s -> Support
  supp1 = supp1gen

  supply1 :: (s -> Supply) -> f s -> Supply
  default supply1 :: Deciding1 Nominal f => (s -> Supply) -> f s -> Supply
  supply1 = supply1gen

instance Nominal1 []
instance Nominal1 Maybe
instance Nominal1 Proxy
instance Nominal a => Nominal1 ((,) a)
instance (Nominal a, Nominal b) => Nominal1 ((,,) a b)
instance (Nominal a, Nominal b, Nominal c) => Nominal1 ((,,,) a b c)
instance Nominal a => Nominal1 (Either a)

-- (#) :: (Nominal a, Nominal b) => a -> b -> Bool
-- a # b = supp a `disjoint` supp b

--------------------------------------------------------------------------------
-- * Fresh
--------------------------------------------------------------------------------

class Fresh a where
  refresh :: Supply -> (a, Supply)

fresh :: (Nominal s, Fresh a) => s -> a
fresh = fst . refresh . supply

instance Fresh Name where
  refresh (Supply a) = (a, Supply $ a+1)

instance Fresh () where
  refresh = (,) ()

instance (Fresh a, Fresh b) => Fresh (a, b) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh a, Fresh b, Fresh c) => Fresh (a, b, c) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> ((a,b,c),ds)

instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a, b, c, d) where
  refresh as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> case refresh ds of
          (d,es) -> ((a,b,c,d),es)

--------------------------------------------------------------------------------
-- * Lifted Fresh
--------------------------------------------------------------------------------

class Fresh1 f where
  refresh1 :: (Supply -> (a, Supply)) -> Supply -> (f a, Supply)

instance Fresh a => Fresh1 ((,) a) where
  refresh1 f as = case refresh as of
    (a,bs) -> case f bs of
      (b,cs) -> ((a,b),cs)

instance (Fresh a, Fresh b) => Fresh1 ((,,) a b) where
  refresh1 f as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case f cs of
         (c,ds) -> ((a,b,c),ds)

instance (Fresh a, Fresh b, Fresh c) => Fresh1 ((,,,) a b c) where
  refresh1 f as = case refresh as of
    (a,bs) -> case refresh bs of
      (b,cs) -> case refresh cs of
        (c,ds) -> case f ds of
          (d,es) -> ((a,b,c,d),es)

--------------------------------------------------------------------------------
-- * Nominal Semigroups
--------------------------------------------------------------------------------

-- | (<>) is a nominal morphism, @a@ is a semigroup in @Nom_fs@
--
-- This implies perm is a distributive group action
--
-- @
-- perm p (a <> b) = perm p a <> perm p b
-- supp (a <> b) ⊆ (supp a <> supp b)
-- @
--
class (Nominal a, Semigroup a) => NominalSemigroup a where
instance NominalSemigroup Set
instance NominalSemigroup Permutation

instance (NominalSemigroup a, NominalSemigroup b) => NominalSemigroup (a, b)
instance NominalSemigroup Support

--------------------------------------------------------------------------------
-- * Nominal Monoids
--------------------------------------------------------------------------------

-- | perm is a unital group action
--
-- @
-- perm p mempty = mempty
-- supp mempty = mempty -- mempty has empty support
-- @
class (NominalSemigroup a, Monoid a) => NominalMonoid a
instance NominalMonoid Permutation
instance NominalMonoid Set
instance (NominalMonoid a, NominalMonoid b) => NominalMonoid (a, b)

-- TODO: Nominal lattices, etc?

--------------------------------------------------------------------------------
-- * GHC Generics Support
--------------------------------------------------------------------------------

class GPermutable f where
  gtrans :: Name -> Name -> f a -> f a
  gperm :: Permutation -> f a -> f a

instance Permutable c => GPermutable (K1 i c) where
  gtrans i j (K1 a) = K1 (trans i j a)
  gperm p (K1 a) = K1 (perm p a)

instance GPermutable f => GPermutable (M1 i c f) where
  gtrans i j (M1 a) = M1 (gtrans i j a)
  gperm p (M1 a) = M1 (gperm p a)

instance GPermutable V1 where
  gtrans _ _ !v = case v of {}
  gperm _ !v = case v of {}

instance GPermutable U1 where
  gtrans _ _ U1 = U1
  gperm _ U1 = U1

instance (GPermutable f, GPermutable g) => GPermutable (f :*: g) where
  gtrans i j (a :*: b) = gtrans i j a :*: gtrans i j b
  gperm p (a :*: b) = gperm p a :*: gperm p b

instance (GPermutable f, GPermutable g) => GPermutable (f :+: g) where
  gtrans i j (L1 a) = L1 (gtrans i j a)
  gtrans i j (R1 a) = R1 (gtrans i j a)
  gperm p (L1 a) = L1 (gperm p a)
  gperm p (R1 a) = R1 (gperm p a)

instance (Permutable1 f, GPermutable g) => GPermutable (f :.: g) where
  gtrans i j (Comp1 a) = Comp1 (trans1 gtrans i j a)
  gperm p (Comp1 a) = Comp1 (perm1 gperm p a)

class GPermutable1 f where
  gtrans1 :: (Name -> Name -> a -> a) -> Name -> Name -> f a -> f a
  gperm1 :: (Permutation -> a -> a) -> Permutation -> f a -> f a

instance Permutable c => GPermutable1 (K1 i c) where
  gtrans1 _ i j (K1 a) = K1 (trans i j a)
  gperm1 _ p (K1 a) = K1 (perm p a)

instance GPermutable1 f => GPermutable1 (M1 i c f) where
  gtrans1 f i j (M1 a) = M1 (gtrans1 f i j a)
  gperm1 f p (M1 a) = M1 (gperm1 f p a)

instance GPermutable1 V1 where
  gtrans1 _ _ _ !v = case v of {}
  gperm1 _ _ !v = case v of {}

instance GPermutable1 U1 where
  gtrans1 _ _ _ U1 = U1
  gperm1 _ _ U1 = U1

instance (GPermutable1 f, GPermutable1 g) => GPermutable1 (f :*: g) where
  gtrans1 f i j (a :*: b) = gtrans1 f i j a :*: gtrans1 f i j b
  gperm1 f p (a :*: b) = gperm1 f p a :*: gperm1 f p b

instance (GPermutable1 f, GPermutable1 g) => GPermutable1 (f :+: g) where
  gtrans1 f i j (L1 a) = L1 (gtrans1 f i j a)
  gtrans1 f i j (R1 a) = R1 (gtrans1 f i j a)
  gperm1 f p (L1 a) = L1 (gperm1 f p a)
  gperm1 f p (R1 a) = R1 (gperm1 f p a)

instance (Permutable1 f, GPermutable1 g) => GPermutable1 (f :.: g) where
  gtrans1 f i j (Comp1 a) = Comp1 (trans1 (gtrans1 f) i j a)
  gperm1 f p (Comp1 a) = Comp1 (perm1 (gperm1 f) p a)

instance GPermutable1 Par1 where
  gtrans1 f i j (Par1 a) = Par1 (f i j a)
  gperm1 f p (Par1 a) = Par1 (f p a)

instance Permutable1 f => GPermutable1 (Rec1 f) where
  gtrans1 f i j (Rec1 a) = Rec1 (trans1 f i j a)
  gperm1 f p (Rec1 a) = Rec1 (perm1 f p a)

--------------------------------------------------------------------------------
-- * Computing permutations from perm-sets
--------------------------------------------------------------------------------

data Binder a = Binder { getBinder :: a -> a -> Maybe Permutation }

instance Contravariant Binder where
  contramap f (Binder g) = Binder $ \x y -> g (f x) (f y)

instance Divisible Binder where
  conquer = Binder $ \ _ _ -> Just mempty
  divide f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    (b, c) -> case f y of
       (d, e) -> (<>) <$> g b d <*> h c e

instance Decidable Binder where
  lose f = Binder $ absurd . f
  choose f (Binder g) (Binder h) = Binder $ \x y -> case f x of
    Left b -> case f x of
      Left d -> g b d
      Right _ -> Nothing
    Right c -> case f y of
      Left _ -> Nothing
      Right e -> h c e

--------------------------------------------------------------------------------
-- * Bindings
--------------------------------------------------------------------------------

-- assumption: all variables in a binding are distinct
class Nominal a => Binding a where
  binding :: a -> a -> Maybe Permutation
  default binding :: Deciding Binding a => a -> a -> Maybe Permutation
  binding a b = getBinder (deciding (Proxy :: Proxy Binding) (Binder binding)) a b

  bv :: a -> Set
  default bv :: Deciding Binding a => a -> Set
  bv = getOp $ deciding (Proxy :: Proxy Binding) $ Op bv

instance Binding Name where
  binding a b = Just (swap a b)
  bv = Set.singleton

instance Binding () where
  binding _ _ = Just mempty
  bv = mempty

instance Binding Void where
  binding = absurd
  bv = absurd

instance Binding Int where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance Binding Bool where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance Binding Char where
  binding a b = mempty <$ guard (a == b)
  bv = mempty

instance (Binding a, Binding b) => Binding (a, b)
instance (Binding a, Binding b, Binding c) => Binding (a, b, c)
instance (Binding a, Binding b, Binding c, Binding d) => Binding (a, b, c, d)
instance (Binding a, Binding b) => Binding (Either a b)
instance Binding a => Binding (Maybe a)
instance Binding a => Binding [a]

--------------------------------------------------------------------------------
-- * Lifted Bindings
--------------------------------------------------------------------------------

class Nominal1 f => Binding1 f where
  binding1 :: (a -> a -> Maybe Permutation) -> f a -> f a -> Maybe Permutation
  default binding1 :: Deciding1 Binding f => (a -> a -> Maybe Permutation) -> f a -> f a -> Maybe Permutation
  binding1 f a b = getBinder (deciding1 (Proxy :: Proxy Binding) (Binder binding) (Binder f)) a b

  bv1 :: (a -> Set) -> f a -> Set
  default bv1 :: Deciding1 Binding f => (a -> Set) -> f a -> Set
  bv1 f = getOp $ deciding1 (Proxy :: Proxy Binding) (Op bv) (Op f)

instance Binding a => Binding1 (Either a)
instance Binding a => Binding1 ((,) a)
instance (Binding a, Binding b) => Binding1 ((,,) a b)
instance (Binding a, Binding b, Binding c) => Binding1 ((,,,) a b c)
instance Binding1 []
instance Binding1 Maybe

-- things that would need [Permutation]:
-- Binding Set isn't really possible, it'd need to give back several possible matchings, using, say, [Permutation]
-- Binding Support is worse
-- Binding Permutatation -- takes permutations to permutations but would need to choose which one of each cycle of the same length was which
-- Binding1 Map
-- Binding1 Trie

--------------------------------------------------------------------------------
-- * Irrefutable Matches
--------------------------------------------------------------------------------

class Binding a => Irrefutable a where
  match :: a -> a -> Permutation

instance Irrefutable Name where
  match = swap -- TODO: move this far enough upstream so that match _is_ swap?

instance Irrefutable Void where
  match = absurd

instance Irrefutable () where
  match _ _ = mempty

instance (Irrefutable a, Irrefutable b) => Irrefutable (a, b) where
  match (a,b) (c,d) = match a c <> match b d

instance (Irrefutable a, Irrefutable b, Irrefutable c) => Irrefutable (a, b, c) where
  match (a,b,c) (d,e,f) = match a d <> match b e <> match c f

instance (Irrefutable a, Irrefutable b, Irrefutable c, Irrefutable d) => Irrefutable (a, b, c, d) where
  match (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> match d h

--------------------------------------------------------------------------------
-- * Lifted Irrefutable Matches
--------------------------------------------------------------------------------

class Binding1 f => Irrefutable1 f where
  match1 :: (a -> a -> Permutation) -> f a -> f a -> Permutation

instance (Irrefutable a) => Irrefutable1 ((,) a) where
  match1 f (a,b) (c,d) = match a c <> f b d

instance (Irrefutable a, Irrefutable b) => Irrefutable1 ((,,) a b) where
  match1 g (a,b,c) (d,e,f) = match a d <> match b e <> g c f

instance (Irrefutable a, Irrefutable b, Irrefutable c) => Irrefutable1 ((,,,) a b c) where
  match1 i (a,b,c,d) (e,f,g,h) = match a e <> match b f <> match c g <> i d h
