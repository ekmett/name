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

module Nominal.Tie where

import Control.Lens hiding (to, from)
import Nominal.Atom
import Nominal.Class
import Nominal.Permutation
import Nominal.Support

-- tie is a fully faithful functor from Nom -> Nom

infixr 6 :><
data Tie a = Atom :>< a
  deriving (Show) -- TODO: fix Eq to be nominal

infixr 6 +>
(+>) :: Atom -> Support -> Support
(+>) = insert

instance (Eq a, Nominal a) => Eq (Tie a) where
  a :>< as == b :>< bs = act (swap c a) as == act (swap c b) bs where
    c = fresh1 (a +> b +> supp as <> supp bs)

instance Act a => Act (Tie a) where
  act s (a :>< b) = act s a :>< act s b

-- nominal
ziptie :: (Nominal x, Nominal y) => Tie x -> Tie y -> Tie (x, y)
ziptie (a :>< as) (b :>< bs) = c :>< (act (swap c a) as, act (swap c b) bs) where
  c = fresh1 (a +> b +> supp as <> supp bs)

-- can i use compiling to categories?

-- nominal
unziptie :: Tie (x, y) -> (Tie x, Tie y)
unziptie (a :>< (x,y)) = (a :>< x, a :>< y)

-- nominal arrow
zipe :: Either (Tie x) (Tie y) -> Tie (Either x y)
zipe (Left (a :>< as)) = a :>< Left as
zipe (Right (a :>< as)) = a :>< Right as

-- nominal arrow
unzipe :: Tie (Either x y) -> Either (Tie x) (Tie y)
unzipe (a :>< Left as) = Left (a :>< as)
unzipe (a :>< Right bs) = Right (a :>< bs)

{-
data Nom a b where
  Nom :: (Nominal a, Nominal b) => { runNum :: a -> b } -> Nom a b

idAtom :: Nom Atom Atom
idAtom = Nom id

instance (Nominal a, Nominal b) => Act (Nom a b) where
  act p (Nom f) = Nom (act p . f . act (inv p))
-}

instance Nominal a => Nominal (Tie a) where
  supp (a :>< b) = supp b & contains a .~ False


