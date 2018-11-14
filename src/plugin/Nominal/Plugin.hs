{-# language CPP #-}
{-# language TypeFamilies #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleInstances #-}
{-# options_ghc -Wno-orphans #-}

---------------------------------------------------------------------------------
-- |
-- Copyright :  (c) Edward Kmett 2018
-- License   :  BSD-2-Clause OR Apache-2.0
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
---------------------------------------------------------------------------------

-- throwaway code for trying to use the compiling to categories stuff to work for me
module Nominal.Plugin where

import Data.Constraint hiding ((***))
import ConCat.Category
import Nominal.Class
import Nominal.Set
import Nominal.Tie
import Prelude hiding (id,(.))

data Nom a b = Nom Set (a -> b)

runNom :: Nom a b -> a -> b
runNom (Nom _ f) = f

instance (Perm a, Perm b) => Perm (Nom a b) where
  perm p (Nom s f) = Nom (perm p s) (perm p f)

instance (Perm a, Perm b) => Nominal (Nom a b) where
  supp (Nom s _) = s

instance Category Nom where
  type Ok Nom = Nominal
  id = Nom mempty id
  Nom x f . Nom y g = Nom (x <> y) (f . g)

-- products

instance OpCon (->) (Sat Perm) where
  inOp = Entail (Sub Dict)

#ifndef ExpAsCat 
-- evil orphan lies needed in order to try out concat
instance OpCon (->) (Sat Nominal) where
  inOp = Entail (Sub Dict) -- lies

instance (Perm a, Perm b) => Nominal (a -> b) where 
  supp = mempty -- lies
#endif

instance OpCon (,) (Sat Nominal) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance AssociativePCat Nom where
  lassocP = Nom mempty $ \ (a,(b,c)) -> ((a,b),c)
  {-# inline lassocP #-}
  rassocP = Nom mempty $ \ ((a,b),c) -> (a,(b,c))
  {-# inline rassocP #-}

instance ProductCat Nom where
  exl = Nom mempty fst
  {-# inline exl #-}
  exr = Nom mempty snd
  {-# inline exr #-}
  dup = Nom mempty dup
  {-# inline dup #-}

instance BraidedPCat Nom where
  swapP = Nom mempty swapP
  {-# inline swapP #-}

instance MonoidalPCat Nom where
  Nom s f *** Nom t g = Nom (s <> t) (f *** g)
  {-# inline (***) #-}
  first (Nom k f) = Nom k (first f)
  {-# inline first #-}
  second (Nom k f) = Nom k (second f)
  {-# inline second #-}

instance TerminalCat Nom where
  it = Nom mempty it

-- sums

instance OpCon Either (Sat Nominal) where
  inOp = Entail (Sub Dict)
  {-# inline inOp #-}

instance AssociativeSCat Nom where
  lassocS = Nom mempty lassocS
  {-# inline lassocS #-}
  rassocS = Nom mempty rassocS
  {-# inline rassocS #-}

instance BraidedSCat Nom where
  swapS = Nom mempty swapS
  {-# inline swapS #-}

instance MonoidalSCat Nom where
  Nom s f +++ Nom t g = Nom (s <> t) (f +++ g)
  {-# INLINE (+++) #-}
  left (Nom s f) = Nom s (left f)
  {-# INLINE left #-}
  right (Nom s f) = Nom s (right f)
  {-# INLINE right #-}

instance CoproductCat Nom  where
  inl = Nom mempty inl
  inr = Nom mempty inr
  jam = Nom mempty jam

-- exponentials

instance OpCon Nom (Sat Nominal) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance Nominal b => ConstCat Nom b where
  const b = Nom (supp b) $ \_ -> b
  unitArrow b = Nom (supp b) $ \_ -> b

-- instance LoopCat Nom where
--   loop (Nom supp f) = Nom supp (loop f)
  
instance TracedCat Nom where
  trace (Nom s f) = Nom s (trace f)

instance ClosedCat Nom where
  -- expects ExpAsCat
#ifdef ExpAsCat
  apply = Nom mempty $ \ (f,x) -> runNom f x
  curry (Nom s f) = Nom s $ \a -> Nom s $ \b -> f (a,b)
  uncurry (Nom s f) = Nom s $ \(a,b) -> f a b
#else
  apply = Nom mempty $ \ (f,x) -> f x
  curry (Nom s f) = Nom s $ \a b -> f (a,b)
  uncurry (Nom s f) = Nom s $ \(a,b) -> f a b
#endif

instance UnitCat Nom where
  lunit = Nom mempty lunit
  lcounit = Nom mempty lcounit
  runit = Nom mempty runit
  rcounit = Nom mempty rcounit

instance DistribCat Nom where
  distl = Nom mempty distl
  distr = Nom mempty distr

-- IxCoproductPCat

instance FiniteCat Nom where
  unFinite = Nom mempty unFinite
  unsafeFinite = Nom mempty unsafeFinite

instance OkFunctor Nom Tie where
  okFunctor = Entail (Sub Dict) 

{-
-- the Functor instance gets in the way
instance FunctorCat Nom Tie where
  fmapC (Nom s f) = Nom s $ \(v :>< a) -> v :>< f a
  unzipC = Nom mempty unziptie
-}

{-
-- instance Zip Tie gets in the way
instance ZipCat Nom Tie where
  zipC = Nom mempty $ \(u :>< a, v :>< b) -> let w = fresh1 (u +> v +> supp a <> supp b)
    in w :>< (a,b)
-}

instance ZapCat Nom Tie where
  -- Tie (Nom a b) <-> Nom (Tie a) (Tie b) is a standard result from Pitts
  zapC (_ :>< Nom _ f) = Nom mempty $ \(v :>< a) -> v :>< f a

instance Nominal a => PointedCat Nom Tie a where
  -- note: this is only okay because the :>< operator explicitly removes the new variable from the support list!
  pointC = Nom mempty $ \a -> fresh1 (supp a) :>< a

instance OkFunctor Nom [] where
  okFunctor = Entail (Sub Dict) 

instance FunctorCat Nom [] where
  fmapC (Nom s f) = Nom s (fmap f)
  unzipC = Nom mempty unzip

instance OkFunctor Nom Maybe where
  okFunctor = Entail (Sub Dict) 

instance FunctorCat Nom Maybe where
  fmapC (Nom s f) = Nom s (fmap f)
  unzipC = Nom mempty $ \case
    Just (a,b) -> (Just a, Just b)
    Nothing -> (Nothing, Nothing)

instance OkIxProd Nom Tie where
  okIxProd = Entail (Sub Dict)

instance IxMonoidalPCat Nom Tie where
  crossF (_ :>< Nom _ f) = Nom mempty $ \(v :>< a) -> v :>< f a

-- broken without ExpAsCat
#ifdef ExpAsCat
instance IxProductCat Nom Tie where
  exF = A 0 :>< Nom mempty $ \(_ :>< a) -> a
  forkF (v :>< Nom s f) = Nom (delete v s) $ (v :><) . f  -- ?
  replF = Nom mempty $ \a -> fresh1 (supp a) :>< a
#endif

-- IxCoproductPCat?

-- instance (Generic1 f, GNominal (Rep1 f)) => FunctorCat Nom f? -- almost works

-- instance NominalFunctor f => FunctorCat Nom f where -- probably better

-- instance (NominalDistributive g, NominalFunctor f) => DistributiveCat Nom g f where

--instance FlipCat Nom where
--  flipC  (Nom s abc) b = Nom (supp b <> s) $ \a -> abc a b  -- this direction is sound
--  flipC' b_nac b = Nom mempty $ \a -> abc a b  -- this direction is dangerous
  
-- Just broken, Counit should be Void
-- instance CoterminalCat Nom where ti = Nom mempty ti

