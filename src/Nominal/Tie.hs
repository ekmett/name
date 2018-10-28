{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language TypeFamilies #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language DefaultSignatures #-}
{-# language PatternSynonyms #-}
{-# language GeneralizedNewtypeDeriving #-}
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

module Nominal.Tie where

import Control.Lens hiding (to, from)
import Nominal.Atom
import Nominal.Class
import Nominal.Permutation
import Nominal.Set

-- tie is a fully faithful functor from Nom -> Nom

infixr 6 :><
data Tie a = Atom :>< a deriving Show

instance (Eq a, Nominal a) => Eq (Tie a) where
  a :>< as == b :>< bs = perm (swap c a) as == perm (swap c b) bs where
    c = fresh1 (a +> b +> supp as <> supp bs)

instance Perm a => Perm (Tie a) where
  perm s (a :>< b) = perm s a :>< perm s b

instance Perm1 Tie where
  perm1 f s (a :>< b) = perm s a :>< f s b

instance Nominal a => Nominal (Tie a) where
  supp (a :>< b) = supp b & contains a .~ False

-- nominal
ziptie :: (Nominal x, Nominal y) => Tie x -> Tie y -> Tie (x, y)
ziptie (a :>< as) (b :>< bs) = c :>< (perm (swap c a) as, perm (swap c b) bs) where
  c = fresh1 (a +> b +> supp as <> supp bs)

-- can i use compiling to categories?

-- nominal
unziptie :: Tie (x, y) -> (Tie x, Tie y)
unziptie (a :>< (x,y)) = (a :>< x, a :>< y)

-- nominal
zipe :: Either (Tie x) (Tie y) -> Tie (Either x y)
zipe (Left (a :>< as)) = a :>< Left as
zipe (Right (a :>< as)) = a :>< Right as

-- nominal
unzipe :: Tie (Either x y) -> Either (Tie x) (Tie y)
unzipe (a :>< Left as) = Left (a :>< as)
unzipe (a :>< Right bs) = Right (a :>< bs)

{-
-- TODO: build these as a proper category in their own right
-- and then see if i can't get concat to use _my_ stuff instead
data Nom a b where
  Nom :: (Nominal a, Nominal b) => Set -> (a -> b) -> Nom a b

runNom :: Nom a b -> a -> b

class N k where
  nom :: Set -> (a -> b) -> k a b

instance N (->) where
  nom _ = id

instance N Nom where
  nom = Nom

idAtom :: Nom Atom Atom
idAtom = Nom id

instance (Nominal a, Nominal b) => Perm (Nom a b) where
  perm p (Nom s f) = Nom (perm p s) (perm p f)

instance (Nominal a, Nominal b) => Nominal (Nom a b) where
  supp (Nom s _) = s 
-}
