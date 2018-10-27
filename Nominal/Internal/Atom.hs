{-# language GeneralizedNewtypeDeriving #-}

module Nominal.Internal.Atom where

import Numeric.Natural

-- Num is for convenience, only
newtype Atom = A Natural deriving (Eq,Num) 

instance Show Atom where
  showsPrec d (A n) = showsPrec d n

