{-# language ConstraintKinds #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language TypeApplications #-}
{-# language DefaultSignatures #-}
{-# language ScopedTypeVariables #-}
{-# language RankNTypes #-}
{-# language DeriveFunctor #-}
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

module Nominal.Category where

import Control.Applicative (Applicative(..), Alternative(..))
import qualified Control.Arrow as Arrow
import Control.Category
import GHC.Exts
import GHC.Generics
import Data.Kind
import Data.Void
import Nominal.Atom
import Nominal.Class
import Nominal.Support
import qualified Prelude
import Prelude
  ( Either(..)
  , Eq(..), Ord(..), Show(..), Read(..), Maybe(..), Bool(..), Bounded(..), Enum(..)
  , ($)
  , Functor(..), (<$>)
  , Foldable(foldMap)
  , Monoid(..), Semigroup(..)
  )

type (+) = Either

data Nom a b = Nom Support (a -> b)

data Op k a b = Op { getOp :: k b a }
  deriving (Eq,Ord,Show,Read,Generic)

data Core k a b = Core { fwd :: k a b, bwd :: k b a }
  deriving (Eq,Ord,Show,Read,Generic)

invCore :: Core k a b -> Core k b a
invCore (Core f g) = Core g f

instance Category Nom where
  id = Nom mempty id
  {-# inline id #-}
  Nom s f . Nom t g = Nom (s<>t) (f.g)
  {-# inline (.) #-}

instance Category k => Category (Op k) where
  id = Op id
  {-# inline id #-}
  Op f . Op g = Op (g . f)
  {-# inline (.) #-}

instance Category k => Category (Core k) where
  id = Core id id
  {-# inline id #-}
  Core f g . Core h i = Core (f . h) (i . g)
  {-# inline (.) #-}

instance (Permutable a, Permutable b) => Permutable (Nom a b) where
  trans i j (Nom s f) = Nom (trans i j s) (trans i j f)
  perm p (Nom s f) = Nom (perm p s) (perm p f)

instance (Permutable a, Permutable b) => Nominal (Nom a b) where
  a # Nom s _ = a # s
  supp (Nom s _) = s
  fresh (Nom s _) = fresh s
  equiv (Nom s _) = equiv s

instance Permutable (k b a) => Permutable (Op (k :: * -> * -> *) a b)
instance Nominal (k b a) => Nominal (Op (k :: * -> * -> *) a b)

instance (Permutable (k a b), Permutable (k b a)) => Permutable (Core k a b)
instance (Nominal (k a b), Nominal (k b a)) => Nominal (Core k a b)

sepNom :: Atom -> Nom a b -> Bool
sepNom a (Nom s _) = a # s

suppNom :: Nom a b -> Support
suppNom (Nom s _) = s

runNom :: Nom a b -> a -> b
runNom (Nom _ f) = f

-- unsafe
nom_ :: N k => (a -> b) -> k a b
nom_ = nom mempty

class Category k => MonoidalP k where
  (***)   :: k a b -> k c d -> k (a,c) (b,d)
  first   :: k a b -> k (a,c) (b,c)
  second  :: k c d -> k (a,c) (a,d)
  swapP   :: k (a,b) (b,a)
  lassocP :: k (a,(b,c)) ((a,b),c)
  rassocP :: k ((a,b),c) (a,(b,c))
  lunit   :: k a ((),a)
  lcounit :: k ((),a) a
  runit   :: k a (a,())
  rcounit :: k (a,()) a

instance MonoidalP (->) where
  (***) f g (a,c) = (f a, g c)
  {-# inline (***) #-}
  first f (a, b) = (f a, b)
  {-# inline first #-}
  second g (a, b) = (a, g b)
  {-# inline second #-}
  swapP (a,b) = (b,a)
  {-# inline swapP #-}
  lassocP (a,(b,c)) = ((a,b),c)
  {-# inline lassocP #-}
  rassocP ((a,b),c) = (a,(b,c))
  {-# inline rassocP #-}
  lunit a = ((),a)
  {-# inline lunit #-}
  lcounit = Prelude.snd
  {-# inline lcounit #-}
  runit a = (a,())
  {-# inline runit #-}
  rcounit = Prelude.fst
  {-# inline rcounit #-}

instance MonoidalP Nom where
  Nom s f *** Nom t g = Nom (s <> t) (f *** g)
  {-# inline (***) #-}
  first (Nom s f) = Nom s (first f)
  {-# inline first #-}
  second (Nom s f) = Nom s (second f)
  {-# inline second #-}
  swapP = nom_ swapP
  {-# inline swapP #-}
  lassocP = nom_ lassocP
  {-# inline lassocP #-}
  rassocP = nom_ rassocP
  {-# inline rassocP #-}
  lunit = nom_ lunit
  {-# inline lunit #-}
  lcounit = nom_ lcounit
  {-# inline lcounit #-}
  runit = nom_ runit
  {-# inline runit #-}
  rcounit = nom_ rcounit
  {-# inline rcounit #-}

instance MonoidalP k => MonoidalP (Op k) where
  Op f *** Op g = Op (f *** g)
  {-# inline (***) #-}
  first (Op f) = Op (first f)
  {-# inline first #-}
  second (Op g) = Op (second g)
  {-# inline second #-}
  swapP = Op swapP
  {-# inline swapP #-}
  lassocP = Op rassocP
  {-# inline lassocP #-}
  rassocP = Op lassocP
  {-# inline rassocP #-}
  lunit = Op lcounit
  {-# inline lunit #-}
  runit = Op rcounit
  {-# inline runit #-}
  lcounit = Op lunit
  {-# inline lcounit #-}
  rcounit = Op runit
  {-# inline rcounit #-}

instance MonoidalP k => MonoidalP (Core k) where
  Core f g *** Core h i = Core (f *** h) (g *** i)
  {-# inline (***) #-}
  first (Core f g) = Core (first f) (first g)
  {-# inline first #-}
  second (Core f g) = Core (second f) (second g)
  {-# inline second #-}
  swapP = Core swapP swapP
  {-# inline swapP #-}
  lassocP = Core lassocP rassocP
  {-# inline lassocP #-}
  rassocP = Core rassocP lassocP
  {-# inline rassocP #-}
  lunit = Core lunit lcounit
  {-# inline lunit #-}
  runit = Core runit rcounit
  {-# inline runit #-}
  lcounit = Core lcounit lunit
  {-# inline lcounit #-}
  rcounit = Core rcounit runit
  {-# inline rcounit #-}

class MonoidalP k => Cartesian k where
  exl :: k (a,b) a
  exr :: k (a,b) b
  dup :: k a (a,a)
  it  :: k a ()

(&&&) :: Cartesian k => k a b -> k a c -> k a (b,c)
f &&& g = (f *** g) . dup
{-# inline (&&&) #-}

instance Cartesian (->) where
  exl = Prelude.fst
  {-# inline exl #-}
  exr = Prelude.snd
  {-# inline exr #-}
  dup a = (a,a)
  {-# inline dup #-}
  it _ = ()
  {-# inline it #-}

instance Cartesian Nom where
  exl = nom_ exl
  {-# inline exl #-}
  exr = nom_ exr
  {-# inline exr #-}
  dup = nom_ dup
  {-# inline dup #-}
  it = nom_ it
  {-# inline it #-}

class Category k => MonoidalS k where
  (+++)    :: k a b -> k c d -> k (a+c) (b+d)
  left     :: k a b -> k (a+c) (b+c)
  right    :: k c d -> k (a+c) (a+d)
  swapS    :: k (a+b) (b+a)
  lassocS  :: k (a+(b+c)) ((a+b)+c)
  rassocS  :: k ((a+b)+c) (a+(b+c))
  lunitS   :: k (Void+a) a
  lcounitS :: k a (Void+a)
  runitS   :: k (a+Void) a
  rcounitS :: k a (a+Void)

instance MonoidalS (->) where
  (+++) = (Arrow.+++)
  {-# INLINE (+++) #-}
  left = Arrow.left
  {-# INLINE left #-}
  right = Arrow.right
  {-# INLINE right #-}
  swapS = Prelude.either Right Left
  {-# inline swapS #-}
  lassocS (Left a) = Left (Left a)
  lassocS (Right (Left b)) = Left (Right b)
  lassocS (Right (Right c)) = Right c
  {-# inline lassocS #-}
  rassocS (Left (Left a)) = Left a
  rassocS (Left (Right b)) = Right (Left b)
  rassocS (Right c) = Right (Right c)
  {-# inline rassocS #-}
  lunitS = Prelude.either ti id
  {-# inline lunitS #-}
  lcounitS = Right
  {-# inline lcounitS #-}
  runitS = Prelude.either id ti
  {-# inline runitS #-}
  rcounitS = Left
  {-# inline rcounitS #-}

instance MonoidalS Nom where
  Nom s f +++ Nom t g = Nom (s <> t) (f +++ g)
  {-# INLINE (+++) #-}
  left (Nom s f) = Nom s (left f)
  {-# INLINE left #-}
  right (Nom s f) = Nom s (right f)
  {-# INLINE right #-}
  swapS = nom_ $ Prelude.either Right Left
  {-# inline swapS #-}
  lassocS = nom_ lassocS
  {-# inline lassocS #-}
  rassocS = nom_ rassocS
  {-# inline rassocS #-}
  lunitS = nom_ lunitS
  {-# inline lunitS #-}
  lcounitS = nom_ lcounitS
  {-# inline lcounitS #-}
  runitS = nom_ runitS
  {-# inline runitS #-}
  rcounitS = nom_ rcounitS
  {-# inline rcounitS #-}

instance MonoidalS k => MonoidalS (Op k) where
  Op f +++ Op g = Op (f +++ g)
  {-# inline (+++) #-}
  left (Op f) = Op (left f)
  {-# inline left #-}
  right (Op g) = Op (right g)
  {-# inline right #-}
  swapS = Op swapS
  {-# inline swapS #-}
  lassocS = Op rassocS
  {-# inline lassocS #-}
  rassocS = Op lassocS
  {-# inline rassocS #-}
  lunitS = Op lcounitS
  {-# inline lunitS #-}
  runitS = Op rcounitS
  {-# inline runitS #-}
  lcounitS = Op lunitS
  {-# inline lcounitS #-}
  rcounitS = Op runitS
  {-# inline rcounitS #-}

instance MonoidalS k => MonoidalS (Core k) where
  Core f g +++ Core h i = Core (f +++ h) (g +++ i)
  {-# inline (+++) #-}
  left (Core f g) = Core (left f) (left g)
  {-# inline left #-}
  right (Core f g) = Core (right f) (right g)
  {-# inline right #-}
  swapS = Core swapS swapS
  {-# inline swapS #-}
  lassocS = Core lassocS rassocS
  {-# inline lassocS #-}
  rassocS = Core rassocS lassocS
  {-# inline rassocS #-}
  lunitS = Core lunitS lcounitS
  {-# inline lunitS #-}
  runitS = Core runitS rcounitS
  {-# inline runitS #-}
  lcounitS = Core lcounitS lunitS
  {-# inline lcounitS #-}
  rcounitS = Core rcounitS runitS
  {-# inline rcounitS #-}

class MonoidalS k => Cocartesian k where
  inl      :: k a (a+b)
  inr      :: k b (a+b)
  jam      :: k (a+a) a
  ti       :: k Void a

(|||) :: Cocartesian k => k a c -> k b c -> k (Either a b) c
f ||| g = jam . (f +++ g)

instance Cocartesian (->) where
  inl = Left
  {-# inline inl #-}
  inr = Right
  {-# inline inr #-}
  jam = Prelude.either id id
  {-# inline jam #-}
  ti = absurd
  {-# inline ti #-}

instance Cocartesian Nom where
  inl = nom_ inl
  {-# inline inl #-}
  inr = nom_ inr
  {-# inline inr #-}
  jam = nom_ jam
  {-# inline jam #-}
  ti = nom_ absurd
  {-# inline ti #-}

class (MonoidalP k, MonoidalS k) => DistributiveCategory k where
  distr :: k ((u+v),b) ((u,b)+(v,b))
  distl :: k (a,(u+v)) ((a,u)+(a,v))

class (MonoidalP k, MonoidalS k) => OpDistributiveCategory k where
  factorl :: k ((a,b)+(a,c)) (a,(b+c))
  default factorl :: (Cartesian k, Cocartesian k) => k ((a,b)+(a,c)) (a,(b+c))
  factorl = second inl ||| second inr
  {-# inline factorl #-}

  factorr :: k ((u,b)+(v,b)) ((u+v),b)
  default factorr :: (Cartesian k, Cocartesian k) => k ((u,b)+(v,b)) ((u+v),b)
  factorr = first inl ||| first inr
  {-# inline factorr #-}

instance OpDistributiveCategory (->)
instance OpDistributiveCategory Nom

instance DistributiveCategory (->) where
  distr (Left u,b) = Left (u,b)
  distr (Right v,b) = Right (v,b)
  {-# inline distr #-}
  distl (a,Left u) = Left (a,u)
  distl (a,Right v) = Right (a,v)
  {-# inline distl #-}

instance DistributiveCategory Nom where
  distr = nom_ distr
  {-# inline distr #-}
  distl = nom_ distl
  {-# inline distl #-}

instance OpDistributiveCategory k => DistributiveCategory (Op k) where
  distr = Op factorr
  {-# inline distr #-}
  distl = Op factorl
  {-# inline distl #-}

instance DistributiveCategory k => OpDistributiveCategory (Op k) where
  factorr = Op distr
  {-# inline factorr #-}
  factorl = Op distl
  {-# inline factorl#-}

instance (DistributiveCategory k, OpDistributiveCategory k) => DistributiveCategory (Core k) where
  distr = Core distr factorr
  {-# inline distr #-}
  distl = Core distl factorl
  {-# inline distl #-}

instance (DistributiveCategory k, OpDistributiveCategory k) => OpDistributiveCategory (Core k) where
  factorr = Core factorr distr
  {-# inline factorr #-}
  factorl = Core factorl distl
  {-# inline factorl #-}

class Cartesian k => CCC k where
  apply     :: k (k a b , a) b
  uncurry   :: k a (k b c) -> k (a,b) c
  type Ob k :: Type -> Constraint
  curry     :: Ob k a => k (a,b) c -> k a (k b c)
  const     :: Ob k a => k a (k b a)
  unitArrow :: Ob k a => k a (k () a)

class Trivial a
instance Trivial a

instance CCC (->) where
  type Ob (->) = Trivial
  apply (f,x) = f x
  {-# inline apply #-}
  curry = Prelude.curry
  {-# inline curry #-}
  uncurry = Prelude.uncurry
  {-# inline uncurry #-}
  const     = Prelude.const
  {-# inline const #-}
  unitArrow = Prelude.const
  {-# inline unitArrow #-}

instance CCC Nom where
  type Ob Nom = Nominal
  apply = nom_ (uncurry runNom)
  {-# inline apply #-}
  curry (Nom s f) = Nom s $ \a -> Nom (s <> supp a) $ \b -> f (a,b) -- note support of environment
  {-# inline curry #-}
  uncurry (Nom s f) = Nom s $ \(a,b) -> runNom (f a) b
  {-# inline uncurry #-}
  const     = Nom mempty $ \a -> Nom (supp a) (const a)
  {-# inline const #-}
  unitArrow = Nom mempty $ \a -> Nom (supp a) (unitArrow a)
  {-# inline unitArrow #-}

niso_ :: NI k => (a -> b) -> (b -> a) -> k a b
niso_ = niso mempty

class (DistributiveCategory k, OpDistributiveCategory k) => NI k where
  niso :: Support -> (a -> b) -> (b -> a) -> k a b

instance NI (->) where
  niso _ f _ = f

instance NI Nom where
  niso s f _ = Nom s f

instance NI k => NI (Op k) where
  niso s f g = Op (niso s g f)

instance NI k => NI (Core k) where
  niso s f g = Core (niso s f g) (niso s g f)

class (NI k, CCC k, Cocartesian k) => N k where
  nom :: Support -> (a -> b) -> k a b
  con :: p k -> (k ~ (->) => r) -> r -> r
  nar :: ((a->b)->(c->d)) -> k a b -> k c d

instance N (->) where
  nom _ = id
  {-# inline nom #-}
  con _ x _ = x
  {-# inline con #-}
  nar = id

instance N Nom where
  nom = Nom
  {-# inline conlike nom #-}
  con _ _ x = x
  {-# inline con #-}
  nar k (Nom s f) = Nom s (k f)

-- Nom is not a tensored category over Hask, so we don't get copowers in general, merely finite ones

class Finite a where
  every :: [a]
  default every :: (Bounded a, Enum a) => [a]
  every = [minBound .. maxBound]
  -- add generics here

instance Finite ()
instance Finite Int
instance Finite Bool

instance Finite Void where
  every = []


instance Finite a => Finite (Maybe a) where
  every = Nothing : (Just <$> every)

instance (Finite a, Finite b) => Finite (a, b) where
  every = (,) <$> every <*> every

instance (Finite a, Finite b) => Finite (Either a b) where
  every = fmap Left every <|> fmap Right every

type (⊙) = Tensor
data Tensor v a = Tensor v a -- v should be 'invisible' within Nom, I give no Nom arrows for extracting it
  deriving (Eq, Functor)

instance Permutable a => Permutable (Tensor v a) where
  trans i j (Tensor v a) = Tensor v (trans i j a)
  perm p (Tensor v a) = Tensor v (perm p a) -- v many copies of a?
  {-# inline perm #-}

instance Nominal a => Nominal (Tensor v a) where
  a # Tensor _ b = a # b
  {-# inline (#) #-}
  supp (Tensor _ a) = supp a
  {-# inline supp #-}
  fresh (Tensor _ a) = fresh a
  {-# inline fresh #-}
  equiv (Tensor _ a) = equiv a
  {-# inline equiv #-}

class Cartesian k => FinitelyTensored k where -- only needs closed monoidal
  mapTensor :: k a b -> k (v ⊙ a) (v ⊙ b)
  tensor   :: k (v ⊙ a) b -> v -> k a b
  untensor :: Finite v => (v -> k a b) -> k (v ⊙ a) b

instance FinitelyTensored Nom where
  mapTensor (Nom s f) = Nom s (fmap f)
  {-# inline mapTensor #-}
  tensor (Nom s f) = Nom s . tensor f
  {-# inline tensor #-}
  untensor f = Nom (foldMap (suppNom . f) every) $ \(Tensor v a) -> runNom (f v) a
  {-# inline untensor #-}

instance FinitelyTensored (->) where
  mapTensor = fmap
  {-# inline mapTensor #-}
  tensor f v = f . Tensor v
  {-# inline tensor #-}
  untensor f (Tensor v a) = f v a
  {-# inline untensor #-}

type (⫛) = Power
data Power v a = Power { runPower :: v -> a } deriving Functor

instance (Finite v, Eq a) => Eq (Power v a) where
  Power f == Power g = fmap f every == fmap g every
  {-# inline (==) #-}

instance Permutable a => Permutable (Power v a) where
  trans i j (Power f) = Power (trans i j . f)
  perm p (Power f) = Power (perm p . f)
  {-# inline perm #-}

instance (Finite v, Nominal a) => Nominal (Power v a) where
  a # Power f = Prelude.all ((a #) . f) every
  {-# inline (#) #-}
  supp (Power f) = foldMap (supp . f) every
  {-# inline supp #-}
  -- default fresh
  equiv (Power f) b c = Prelude.all (\ v -> equiv (f v) b c) every
  {-# inline equiv #-}

class Cartesian k => FinitelyPowered k where
  mapPower :: k a b -> k (v ⫛ a) (v ⫛ b)
  power :: k a (v ⫛ b) -> (v -> k a b)
  unpower :: Finite v => (v -> k a b) -> k a (v ⫛ b) -- messy side-condition

instance FinitelyPowered (->) where
  mapPower = fmap
  {-# inline mapPower #-}
  power f v a = runPower (f a) v
  {-# inline power #-}
  unpower f a = Power $ \v -> f v a
  {-# inline unpower #-}

instance FinitelyPowered Nom where
  mapPower (Nom s f) = Nom s (fmap f)
  {-# inline mapPower #-}
  power (Nom s f) v = Nom s $ \a -> runPower (f a) v
  {-# inline power #-}
  unpower f = Nom (foldMap (suppNom . f) every) $ \ a -> Power $ \v -> runNom (f v) a
  {-# inline unpower #-}
