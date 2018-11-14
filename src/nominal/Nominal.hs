---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal
  ( module Nominal.Atom
  , module Nominal.Category
  , module Nominal.Class
  , module Nominal.Lattice
  , module Nominal.Logic
  -- , module Nominal.Map -- designed for qualified import
  , module Nominal.Permutation
  , module Nominal.Set
  , module Nominal.Substitution
  , module Nominal.Support
  , module Nominal.Suspension
  , module Nominal.Tie
  , Map
  ) where

import Nominal.Atom
import Nominal.Category
import Nominal.Class
import Nominal.Lattice
import Nominal.Logic
import Nominal.Map
import Nominal.Permutation
import Nominal.Set hiding (foldr)
import Nominal.Substitution
import Nominal.Support
import Nominal.Suspension
import Nominal.Tie
