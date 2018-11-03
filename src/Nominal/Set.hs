{-# language BangPatterns #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language LambdaCase #-}
{-# language ConstraintKinds #-}
{-# language DefaultSignatures #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Set where

import Control.Lens
import Control.Monad (guard)
import Data.Maybe (isJust)
import Nominal.Lattice
-- import Nominal.Class
import qualified Nominal.Internal.Trie as Trie
import Nominal.Internal.Trie (Trie, Atom(..))

newtype Set = Set { getSet :: Trie () }
  deriving (Eq, Show)

instance PartialOrder Set where
  Set a ⊆ Set b = Trie.isSubtrieOfBy (\_ _ -> True) a b

instance Semigroup Set where
  Set m <> Set n = Set (Trie.union m n)

instance Monoid Set where
  mempty = Set Empty

instance Join Set
instance BoundedJoin Set

instance Meet Set where
  Set m ∧ Set n = Set (Trie.intersection m n)

instance Distributive Set

instance GBA Set where
  Set m \\ Set n = Set (Trie.diff m n)

instance AsEmpty Set where
  _Empty = prism (const (Set Empty)) $ \case
    Set Empty -> Right ()
    x -> Left x

type instance Index Set = Atom
instance Contains Set where
  contains a f (Set e) = Set <$> at a (fmap guard . f . isJust) e where

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
  insert a (Set t) = Set (Trie.insert a () t)
  delete a (Set t) = Set (Trie.delete a t)
  member a (Set t) = Trie.member a t
  singleton a      = Set (Trie.singleton a ())

disjoint :: Set -> Set -> Bool
disjoint (Set a) (Set b) = Trie.disjoint a b
