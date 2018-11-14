---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Name
  ( module Name.Atom
  , module Name.Category
  , module Name.Class
  , module Name.Lattice
  , module Name.Logic
  -- , module Name.Map -- designed for qualified import
  , module Name.Permutation
  , module Name.Set
  , module Name.Substitution
  , module Name.Support
  , module Name.Suspension
  , module Name.Tie
  , Map
  ) where

import Name.Atom
import Name.Category
import Name.Class
import Name.Lattice
import Name.Logic
import Name.Map
import Name.Permutation
import Name.Set hiding (foldr)
import Name.Substitution
import Name.Support
import Name.Suspension
import Name.Tie
