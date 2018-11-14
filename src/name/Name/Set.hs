{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language LambdaCase #-}
{-# language ConstraintKinds #-}
{-# language DefaultSignatures #-}
{-# language GADTs #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Name.Set where

import Control.Lens
import Control.Monad (guard)
import Data.Functor.Classes
import Data.Maybe (isJust)
import GHC.Exts (IsList(..))
import Name.Lattice
import qualified Name.Internal.Trie as Trie
import Name.Internal.Trie (Trie, Atom(..))
import Unsafe.Coerce

data Set where
  Set :: Trie a -> Set

foldr :: (Atom -> r -> r) -> r -> Set -> r
foldr f z (Set t) = ifoldr (\i _ r -> f i r) z t
{-# inline foldr #-}

instance Eq Set where
  Set x == Set y = liftEq (\_ _ -> True) x y

instance Ord Set where
  Set x `compare` Set y = liftCompare (\_ _ -> EQ) x y

instance Show Set where
  showsPrec d (Set xs) = showsPrec d $ ifoldr (\i _ r -> i:r) [] xs

instance IsList Set where
  type Item Set = Atom
  fromList = Prelude.foldr insert mempty
  toList (Set xs) = ifoldr (\i _ r -> i:r) [] xs
  
instance PartialOrder Set where
  Set a ⊆ Set b = Trie.isSubtrieOfBy (\_ _ -> True) a b

instance Semigroup Set where
  Set m <> Set n = Set (Trie.union m (unsafeCoerce n)) -- evil

instance Monoid Set where
  mempty = Set Empty

instance Join Set

instance BoundedJoin Set

instance Meet Set where
  Set m ∧ Set n = Set (Trie.intersection m n)

instance DistributiveLattice Set

instance GBA Set where
  Set m \\ Set n = Set (Trie.diff m n)

instance AsEmpty Set where
  _Empty = prism (const (Set Empty)) $ \case
    Set Empty -> Right ()
    x -> Left x

type instance Index Set = Atom

instance Contains Set where
  contains a f (Set e) = Set <$> at a (fmap guard' . f . isJust) e where
    guard' :: Bool -> Maybe a
    guard' b = undefined <$ guard b

class (Index a ~ Atom, Contains a) => SetLike a where
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
  default singleton :: BoundedJoin a => Atom -> a
  singleton a = insert a bottom
  {-# inline singleton #-}

infixr 6 +>

(+>) :: SetLike a => Atom -> a -> a
(+>) = insert

instance SetLike Set where
  insert a (Set t) = Set (Trie.insert a undefined t)
  delete a (Set t) = Set (Trie.delete a t)
  member a (Set t) = Trie.member a t
  singleton a      = Set (Trie.singleton a ())

disjoint :: Set -> Set -> Bool
disjoint (Set a) (Set b) = Trie.disjoint a b
