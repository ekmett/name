{-# language DeriveGeneric #-}
{-# language LambdaCase #-}
{-# language DeriveAnyClass #-}
{-# language StrictData #-}
{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}

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

import Control.Lens (prism)
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
  deriving (Show, Eq, Generic, Permutable, Nominal, Binding)

instance AsAtom Pat where
  _Atom = prism PVar $ \case
    PVar v -> Right v
    x -> Left x

data Sig a b = a ::: b
  deriving (Show, Eq, Generic, Generic1, Permutable, Nominal, Permutable1, Nominal1)

instance (Binding a, Nominal b, Eq b) => Binding (Sig a b) where
  binding (a ::: b) (c ::: d) | b == d = binding a c
  binding _ _ = Nothing
  bv (a ::: b) = bv a

instance (Subst e a, Subst e b) => Subst e (Sig a b)

data Kind
  = KVar Atom
  | KType
  | KHole
  | KArr Kind Kind
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsAtom Kind where
  _Atom = prism KVar $ \case
    KVar v -> Right v
    x -> Left x

data Type
  = TVar Atom
  | TInt
  | TArr Type Type
  | TCon Con [Type]
  | THole
  | TForall (Sig Atom Kind ⊸ Type)
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsAtom Type where
  _Atom = prism TVar $ \case
    TVar v -> Right v
    x -> Left x

data Term
  = Var Atom
  | App Term Term
  | Lam (Pat ⊸ Term)
  | Let (Sig Atom Type ⊸ Term) Term
  | Case Term [Pat ⊸ Term]
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsAtom Term where
  _Atom = prism Var $ \case
    Var v -> Right v
    x -> Left x

instance Subst Kind Term
instance Subst Kind Type
instance Subst Type Term
instance Subst Kind Atom where subst _ e = e
instance Nominal e => Subst e Char where subst _ e = e
instance Nominal e => Subst e Int where subst _ e = e
instance Subst Type Atom where subst _ e = e
instance Subst Term Atom where subst _ e = e
instance Subst Term Kind where subst _ e = e
instance Subst Kind Pat  where subst _ e = e
instance Subst Type Pat  where subst _ e = e
instance Subst Term Pat  where subst _ e = e
instance Subst Term Type where subst _ e = e
instance Subst Type Kind where subst _ e = e
