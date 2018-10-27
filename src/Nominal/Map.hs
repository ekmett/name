module Nominal.Map 
( Map
, union         -- :: NominalSemigroup a => Map a -> Map a -> Map a
, intersectWith -- :: (a -> b -> c) -> Map a -> Map b -> Map c
, intersect     -- :: Map a -> Map a -> Map a
, diff          -- :: Map a -> Support -> Map a
, (\\)          -- :: Map a -> Support -> Map a
, lookup        -- :: Atom -> Map a -> Maybe a
, delete        -- :: Atom -> Map a -> Map a
, insert        -- :: Nominal a => Atom -> a -> Map a -> Map a
, singleton     -- :: Nominal a => Atom -> a -> Map a
) where

import Prelude hiding (lookup)
import Nominal.Internal.Map
