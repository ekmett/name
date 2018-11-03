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
import Nominal.Support

-- tie is a fully faithful functor from Nom -> Nom

infixr 6 :><
data Tie a = Atom :>< a deriving Show

instance (Eq a, Nominal a) => Eq (Tie a) where
  a :>< as == b :>< bs = perm (swap c a) as == perm (swap c b) bs where
    c = fresh (supp a <> supp b <> supp as <> supp bs)

instance Permutable a => Permutable (Tie a) where
  perm s (a :>< b) = perm s a :>< perm s b

instance Permutable1 Tie where
  perm1 f s (a :>< b) = perm s a :>< f s b

instance Nominal a => Nominal (Tie a) where
  supp (a :>< b) = case supp b of
    Supp xs -> Supp $ xs & at a .~ Nothing -- merge that element into U

-- nominal
ziptie :: (Nominal x, Nominal y) => Tie x -> Tie y -> Tie (x, y)
ziptie (a :>< as) (b :>< bs) = c :>< (perm (swap c a) as, perm (swap c b) bs) where
  c = fresh (supp a <> supp b <> supp as <> supp bs)

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
