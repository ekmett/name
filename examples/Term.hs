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

module Term where

import GHC.Generics
import Nominal
import Nominal.Category

-- Eq automatically respects alpha-equivalence of bound terms

data Term
  = Var !Atom
  | App !Term !Term
  | Lam !(Tie Term)
  deriving (Eq, Generic)

instance Permutable Term
instance Nominal Term

subst :: N k => k Atom Term -> k Term Term
subst = nar $ \f -> \case
  Var a -> f a
  App l r -> App (subst f l) (subst f r)
  Lam t -> Lam (subst f <$> t)
