---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Data.Name
  ( module Data.Name.Category
  , module Data.Name.Class
  , module Data.Name.Lattice
  , module Data.Name.Logic
  -- , module Data.Name.Map -- designed for qualified import
  , module Data.Name.Permutation
  , module Data.Name.Set
  , module Data.Name.Substitution
  , module Data.Name.Support
  , module Data.Name.Suspension
  , module Data.Name.Tie
  , module Data.Name.Type
  , Map
  ) where

import Data.Name.Category
import Data.Name.Class
import Data.Name.Lattice
import Data.Name.Logic
import Data.Name.Map
import Data.Name.Permutation
import Data.Name.Set hiding (foldr)
import Data.Name.Substitution
import Data.Name.Support
import Data.Name.Suspension
import Data.Name.Tie
import Data.Name.Type
