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
import Data.Name
import GHC.Generics

-- Eq automatically respects alpha-equivalence of bound terms

type Con = String

data Pat
  = PWild
  | PVar Name
  | PCon Con [Pat]
  | PLit Int
  deriving (Show, Eq, Generic, Permutable, Nominal, Binding)

instance AsName Pat where
  _Name = prism PVar $ \case
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
  = KVar Name
  | KType
  | KHole
  | KArr Kind Kind
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsName Kind where
  _Name = prism KVar $ \case
    KVar v -> Right v
    x -> Left x

data Type
  = TVar Name
  | TInt
  | TArr Type Type
  | TCon Con [Type]
  | THole
  | TForall (Sig Name Kind ⊸ Type)
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsName Type where
  _Name = prism TVar $ \case
    TVar v -> Right v
    x -> Left x

data Term
  = Var Name
  | App Term Term
  | Lam (Pat ⊸ Term)
  | Let (Sig Name Type ⊸ Term) Term
  | Case Term [Pat ⊸ Term]
  deriving (Show, Eq, Generic, Permutable, Nominal)

instance AsName Term where
  _Name = prism Var $ \case
    Var v -> Right v
    x -> Left x

instance Subst Kind Term
instance Subst Kind Type
instance Subst Type Term
instance Subst Kind Name where subst _ e = e
instance Nominal e => Subst e Char where subst _ e = e
instance Nominal e => Subst e Int where subst _ e = e
instance Subst Type Name where subst _ e = e
instance Subst Term Name where subst _ e = e
instance Subst Term Kind where subst _ e = e
instance Subst Kind Pat  where subst _ e = e
instance Subst Type Pat  where subst _ e = e
instance Subst Term Pat  where subst _ e = e
instance Subst Term Type where subst _ e = e
instance Subst Type Kind where subst _ e = e
