{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language TypeOperators #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}

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

import Control.Lens
import GHC.Generics
import Name

-- Eq automatically respects alpha-equivalence of bound terms

data Term
  = Var !Atom
  | App !Term !Term
  | Lam !(Atom ⊸ Term)
  deriving (Eq, Show, Generic, Permutable, Nominal)

instance Subst Term Atom where
  subst _ e = e

instance AsAtom Term where
  _Atom = prism Var $ \case
    Var v -> Right v
    x -> Left x

substTerm :: Map Term -> Term -> Term
substTerm = subst 
