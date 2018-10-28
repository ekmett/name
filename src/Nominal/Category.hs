{-# language ConstraintKinds #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language FlexibleInstances #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
{-# language DeriveFunctor #-}

module Nominal.Category where

import Control.Applicative (Applicative(..), Alternative(..))
import qualified Control.Arrow as Arrow
import Control.Category
import GHC.Exts
import Data.Void
import Nominal.Class
import Nominal.Set
import qualified Prelude
import Prelude
  ( Either(..), Eq(..), Maybe(..), Bool(..), ($)
  , Functor(..), (<$>)
  , Foldable(foldMap)
  , Monoid(..), Semigroup(..)
  )

-- Here i don't need Ob constraints until i get to things that
-- touch the environment in Cartesian so i delay incurring any costs for
-- that part til i get there

type (*) = (,)
type (+) = Either

data Nom a b = Nom Set (a -> b)

instance (Perm a, Perm b) => Perm (Nom a b) where
  perm p (Nom s f) = Nom (perm p s) (perm p f)

instance (Perm a, Perm b) => Nominal (Nom a b) where
  supp (Nom s _) = s

suppNom :: Nom a b -> Set
suppNom (Nom s _) = s

runNom :: Nom a b -> a -> b
runNom (Nom _ f) = f

-- used to construct nominal morphisms that have no dependencies, unsafe
nom_ :: (a -> b) -> Nom a b
nom_ = Nom mempty

-- generally the names are chosen to line up with conal's plugin
-- we can be compatible with 'base's Category this way

instance Category Nom where
  id = Nom mempty id
  {-# inline id #-}
  Nom s f . Nom t g = Nom (s<>t) (f.g)
  {-# inline (.) #-}

class Category k => Cartesian k where
  (***)   :: k a b -> k c d -> k (a*c) (b*d)
  first   :: k a b -> k (a*c) (b*c)
  second  :: k c d -> k (a*c) (a*d)
  swapP   :: k (a*b) (b*a)
  lassocP :: k (a*(b*c)) ((a*b)*c)
  rassocP :: k ((a*b)*c) (a*(b*c))
  exl     :: k (a*b) a
  exr     :: k (a*b) b
  dup     :: k a (a*a)
  lunit   :: k a (()*a)
  lcounit :: k (()*a) a
  runit   :: k a (a*())
  rcounit :: k (a*()) a
  it      :: k a ()

instance Cartesian (->) where
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
  exl = Prelude.fst
  {-# inline exl #-}
  exr = Prelude.snd
  {-# inline exr #-}
  dup a = (a,a)
  {-# inline dup #-}
  lunit a = ((),a)
  {-# inline lunit #-}
  lcounit = Prelude.snd
  {-# inline lcounit #-}
  runit a = (a,())
  {-# inline runit #-}
  rcounit = Prelude.fst
  {-# inline rcounit #-}
  it _ = ()
  {-# inline it #-}

instance Cartesian Nom where
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
  exl = nom_ exl
  {-# inline exl #-}
  exr = nom_ exr
  {-# inline exr #-}
  dup = nom_ dup
  {-# inline dup #-}
  lunit = nom_ lunit
  {-# inline lunit #-}
  lcounit = nom_ lcounit
  {-# inline lcounit #-}
  runit = nom_ runit
  {-# inline runit #-}
  rcounit = nom_ rcounit
  {-# inline rcounit #-}
  it = nom_ it
  {-# inline it #-}

class Category k => Cocartesian k where
  (+++)    :: k a b -> k c d -> k (a+c) (b+d)
  left     :: k a b -> k (a+c) (b+c)
  right    :: k c d -> k (a+c) (a+d)
  swapS    :: k (a+b) (b+a)
  lassocS  :: k (a+(b+c)) ((a+b)+c)
  rassocS  :: k ((a+b)+c) (a+(b+c))
  inl      :: k a (a+b)
  inr      :: k b (a+b)
  jam      :: k (a+a) a
  lunitS   :: k (Void+a) a
  lcounitS :: k a (Void+a)
  runitS   :: k (a+Void) a
  rcounitS :: k a (a+Void)
  ti       :: k Void a

instance Cocartesian (->) where
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
  inl = Left
  {-# inline inl #-}
  inr = Right
  {-# inline inr #-}
  jam = Prelude.either id id
  {-# inline jam #-}
  lunitS = Prelude.either ti id
  {-# inline lunitS #-}
  lcounitS = Right
  {-# inline lcounitS #-}
  runitS = Prelude.either id ti
  {-# inline runitS #-}
  rcounitS = Left
  {-# inline rcounitS #-}
  ti = absurd
  {-# inline ti #-}

instance Cocartesian Nom where
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
  inl = nom_ inl
  {-# inline inl #-}
  inr = nom_ inr
  {-# inline inr #-}
  jam = nom_ jam
  {-# inline jam #-}
  lunitS = nom_ lunitS
  {-# inline lunitS #-}
  lcounitS = nom_ lcounitS
  {-# inline lcounitS #-}
  runitS = nom_ runitS
  {-# inline runitS #-}
  rcounitS = nom_ rcounitS
  {-# inline rcounitS #-}
  ti = nom_ absurd
  {-# inline ti #-}

class Cartesian k => CCC k where
  apply     :: k (k a b * a) b
  uncurry   :: k a (k b c) -> k (a*b) c

  -- pragmatically limit "Ob" constraints to just things we're going to pass into the environment
  -- pushing them here makes GHC do all the work, at the expense of making all the previous statements
  -- about being a real category a bit of a lie. Another way to think about is that both Nom and (->)
  -- are Cartesian, Cocartesian, etc. independent of constraints on the objects they use. But we have
  -- to restrict to some sub-category to handle currying, etc. The classes here capture any category
  -- that respects parametricity, but which has restrictions on what can be put into the environment.

  type Ob k :: * -> Constraint
  curry     :: Ob k a => k (a*b) c -> k a (k b c)
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

-- convenient for writing general purpose code abstract whether it is an arrow or in Nom
class (CCC k, Cocartesian k) => N k where
  nom :: Set -> (a -> b) -> k a b -- construct a nominal arrow with manual support, unsafe

instance N (->) where
  nom _ = id
  {-# inline nom #-}

instance N Nom where
  nom = Nom
  {-# inline conlike nom #-}

-- Nom is not a tensored category over Hask, so we don't get copowers in general, merely finite ones

class Finite a where
  every :: [a]
  -- add generics here

instance Finite Bool where
  every = [False,True]

instance Finite Void where
  every = []

instance Finite () where
  every = [()]

instance Finite a => Finite (Maybe a) where
  every = Nothing : (Just <$> every)

instance (Finite a, Finite b) => Finite (a, b) where
  every = (,) <$> every <*> every

instance (Finite a, Finite b) => Finite (Either a b) where
  every = fmap Left every <|> fmap Right every

type (⊙) = Tensor
data Tensor v a = Tensor v a -- v should be 'invisible' within Nom, I give no Nom arrows for extracting it
  deriving (Eq, Functor)

instance Perm a => Perm (Tensor v a) where
  perm p (Tensor v a) = Tensor v (perm p a) -- v many copies of a?

instance Nominal a => Nominal (Tensor v a) where
  supp (Tensor _ a) = supp a

class Cartesian k => FinitelyTensored k where -- only needs closed monoidal
  mapTensor :: k a b -> k (v ⊙ a) (v ⊙ b)
  tensor   :: k (v ⊙ a) b -> v -> k a b
  untensor :: Finite v => (v -> k a b) -> k (v ⊙ a) b

instance FinitelyTensored Nom where
  mapTensor (Nom s f) = Nom s (fmap f)
  tensor (Nom s f) = Nom s . tensor f
  untensor f = Nom (foldMap (suppNom . f) every) $ \(Tensor v a) -> runNom (f v) a

instance FinitelyTensored (->) where
  mapTensor = fmap
  tensor f v = f . Tensor v
  untensor f (Tensor v a) = f v a

type (⫛) = Power
data Power v a = Power { runPower :: v -> a }
  deriving (Functor)

instance (Finite v, Eq a) => Eq (Power v a) where
  Power f == Power g = fmap f every == fmap g every

instance Perm a => Perm (Power v a) where
  perm p (Power f) = Power (perm p . f)

instance (Finite v, Nominal a) => Nominal (Power v a) where
  supp (Power f) = foldMap (supp . f) every

class Cartesian k => FinitelyPowered k where
  mapPower :: k a b -> k (v ⫛ a) (v ⫛ b)
  power :: k a (v ⫛ b) -> (v -> k a b)
  unpower :: Finite v => (v -> k a b) -> k a (v ⫛ b) -- messy side-condition

instance FinitelyPowered (->) where
  mapPower = fmap
  power f v a = runPower (f a) v
  unpower f a = Power $ \v -> f v a

instance FinitelyPowered Nom where
  mapPower (Nom s f) = Nom s (fmap f)
  power (Nom s f) v = Nom s $ \a -> runPower (f a) v
  unpower f = Nom (foldMap (suppNom . f) every) $ \ a -> Power $ \v -> runNom (f v) a
