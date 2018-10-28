{-# language GeneralizedNewtypeDeriving #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Nominal.Internal.Atom where

import Numeric.Natural

-- Num is for convenience, only
newtype Atom = A Natural deriving (Eq,Num) 

instance Show Atom where
  showsPrec d (A n) = showsPrec d n

