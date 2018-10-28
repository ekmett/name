{-# language DeriveGeneric #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Term where

import Nominal

data Term
  = Var !Atom
  | App !Term !Term
  | Lam !(Tie Term)
  deriving (Eq, Generic)

instance Perm Term
instance Nominal Term

-- Eq respects alpha-equivalence of bound terms
