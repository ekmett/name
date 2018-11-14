{-# language DeriveGeneric #-}
{-# language LambdaCase #-}
{-# language DeriveAnyClass #-}
{-# language StrictData #-}

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
  | PVar Atom
  | PCon Con [Pat]
  | PLit Int
  deriving (Eq, Generic, Permutable, Nominal, Binding)

data Sig a b = a ::: b
  deriving (Eq, Generic, Permutable, Nominal, Permutable1, Nominal1) 

instance (Binding a, Eq b) => Binding (Sig a b) where
  binding (a ::: b) (c ::: d) | b == d = binding a c
  binding _ _ = Nothing

data Kind
  = KType
  | KHole
  | KArr Kind Kind
  deriving (Eq, Generic, Permutable, Nominal)

data Type
  = TInt
  | TArr Type Type
  | TCon Con [Type]
  | THole
  | TForall (Sig Atom Kind ⊸ Type)
  deriving (Eq, Generic, Permutable, Nominal)

data Term
  = Var Atom
  | App Term Term
  | Lam (Pat ⊸ Term)
  | Let (Sig Atom Type ⊸ Term) Term
  | Case Term [Pat ⊸ Term]
  deriving (Eq, Generic, Permutable, Nominal)

subst :: N k => k Atom Term -> k Term Term
subst = nar $ \f -> \case
  Var a -> f a
  App l r -> App (subst f l) (subst f r)
  Lam t -> Lam (subst f <$> t)
