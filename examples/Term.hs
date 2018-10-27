{-# language DeriveGeneric #-}

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
