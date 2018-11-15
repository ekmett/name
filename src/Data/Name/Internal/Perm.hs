{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language PatternSynonyms #-}
{-# language RankNTypes #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name.Internal.Perm where

import Control.Lens
import Control.Monad
import Data.Maybe
import Data.Name.Internal.Trie
import Data.Semigroup (Semigroup(..))
import Prelude hiding (elem, lookup)

newtype Perm = Perm {getPerm :: Trie Name }
  deriving (Eq,Ord,Show)

perm' :: Perm -> Name -> Name
perm' (Perm t) a = fromMaybe a $ lookup a t

inv' :: Perm -> Perm
inv' (Perm x) = Perm $ ifoldr (flip insert) Empty x where

square' :: Perm -> Perm
square' (Perm t) = Perm $ ifilterMap go t where
  go i j = mfilter (i/=) $ lookup j t -- check this

sup' :: Perm -> Maybe Name
sup' (Perm t) = sup t

instance Semigroup Perm where
  --  x       y        z
  --  ----    ----     ------
  --  0->1             0 -> 2
  --  1->0    1->2     1 -> 0
  --          2->1     2 -> 1
  Perm x <> yt@(Perm y) = Perm $ ifilterMap f $ union (perm' yt <$> x) y where
    f i = mfilter (i/=) . pure

elem :: Name -> Lens' Perm Name
elem i f (Perm s) = Perm <$> at i (non i f) s where

instance Monoid Perm where
  mempty = Perm Empty
