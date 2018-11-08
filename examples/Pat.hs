{-# language DeriveGeneric #-}
{-# language LambdaCase #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

module Pat where

import GHC.Generics
import Nominal
import Nominal.Category

-- Eq automatically respects alpha-equivalence of bound terms

type Con = String

data Pat
  = PWild
  | PVar !Atom
  | PCon Con [Pat]
  | PLit !Int
  deriving (Eq, Generic)

instance Permutable Pat
instance Nominal Pat
instance Binding Pat

data Term
  = Var !Atom
  | App !Term !Term
  | Lam !(Tie Atom Term)
  | Case !Term [(Pat, Term)]
  deriving (Eq, Generic)

instance Permutable Term
instance Nominal Term

subst :: N k => k Atom Term -> k Term Term
subst = nar $ \f -> \case
  Var a -> f a
  App l r -> App (subst f l) (subst f r)
  Lam t -> Lam (subst f <$> t)
