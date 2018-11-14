---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Name.Map
( Map
, union            -- :: NominalSemigroup a => Map a -> Map a -> Map a
, intersectionWith -- :: (a -> b -> c) -> Map a -> Map b -> Map c
, intersection     -- :: Map a -> Map a -> Map a
, diff             -- :: Map a -> Set -> Map a
, (\\)             -- :: Map a -> Set -> Map a
, lookup           -- :: Atom -> Map a -> Maybe a
, delete           -- :: Atom -> Map a -> Map a
, insert           -- :: Nominal a => Atom -> a -> Map a -> Map a
, singleton        -- :: Nominal a => Atom -> a -> Map a
) where

import Prelude hiding (lookup)
import Name.Internal.Map
