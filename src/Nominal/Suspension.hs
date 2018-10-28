module Nominal.Suspension where

import Nominal.Class
import Nominal.Permutation

-- semi-direct product of a permutation and a nominal monoid
data Suspended a = Suspended Permutation a 

instance Perm (Suspended a) where
  perm p (Suspended q a) = Suspended (p <> q) a

instance Nominal a => Nominal (Suspended a) where
  supp (Suspended q a) = perm q (supp a)

-- nominal given a nominal morphism -- uses π.(fx) = f(π.x)
nmap :: Perm a => (a -> b) -> Suspended a -> Suspended b
nmap f (Suspended p a) = Suspended p (f a)
-- nmap (Nom s f) = Nom s $ \(Suspended p a) -> Suspended p (f a)

nreturn :: a -> Suspended a
nreturn = Suspended mempty

njoin :: Suspended (Suspended a) -> Suspended a
njoin (Suspended p (Suspended q a)) = Suspended (p <> q) a

-- nominal 
nextract :: Perm a => Suspended a -> a
nextract (Suspended p a) = perm p a

-- Suspended should be a nominal comonad
nduplicate :: Perm a => Suspended a -> Suspended (Suspended a)
nduplicate (Suspended p a) = Suspended p (Suspended mempty a) -- we can meaningfully 'split' bijections as they don't matter in Nom

instance NominalSemigroup a => Semigroup (Suspended a) where
  Suspended p a <> Suspended q b = Suspended (p <> q) (a <> perm p b)
  
instance NominalMonoid a => Monoid (Suspended a) where
  mempty = Suspended mempty mempty


{-
-- this is not a nominal monoid in its own right
-- perm p (Suspended q a) <> perm p (Suspended r b)) = Suspended (p <> q) a <> Suspended (p <> r) a = Suspended (p <> q <> p <> r) ... 

data Semi a = Semi Permutation a

instance Perm (Semi a) where
  perm p (Semi q a) = Semi (act p q) a

instance Nominal a => Nominal (Semi a) where
  supp (Semi q a) = perm q (supp a)

-- same comonad structure

instance NominalSemigroup a => Semigroup (Semi a) where
  mappend (Semi p a) (Semi q b) = Semi (p <> q) (a <> perm p b)
  
instance NominalMonoid a => Monoid (Semi a) where
  mempty = Semi mempty mempty

-- also not a nominal monoid
-- extract (perm p (Semi q a) <> perm p (Semi r b)) =
-- extract (Semi (p <> q <> inv p) a <> Semi (p <> r <> inv p) b) =
-- extract (Semi (p <> q <> inv p <> p <> r <> inv p) (a <> perm (p <> q <> inv p) b)) = 
-- extract (Semi (p <> q <> r <> inv p) (a <> perm (p <> q <> inv p) b)) =
-- perm (p <> q <> r <> inv p) (a <> perm (p <> q <> inv p) b) -- explioit disttrbution
-- perm (p <> q <> r <> inv p) a <> perm (p <> q <> r <> inv p) (perm (p <> q <> inv p) b)
-- perm (p <> q <> r <> inv p) a <> perm (p <> q <> r <> q <> inv p) b
-}
