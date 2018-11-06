module Nominal.Restriction where

import Data.Map.Internal
import Data.Void
import Nominal.Atom
import Nominal.Tie
import Nominal.Internal.Trie

infixr 6 #\

-- | This isn't implementable unless I use some kind of global variable supply
class Nominal x => Restricted x where
  -- |
  -- @
  -- restrict . nreturn = id
  -- restrict . fmap restrict = restrict . fmap restrict . delta
  -- restrict (Tie a x) = a #\ x
  -- @
  restrict :: Tie x -> x
  restrict (Tie a x) = a #\ x

  -- |
  -- @
  -- a # (a #\ x)
  -- a # x ⇒  a #\ x = x
  -- a #\ b #\ x = b #\ a #\ x -- this is a really annoying condition!
  -- @
  -- |
  (#\) :: Atom -> x -> x
  a #\ x = restrict (Tie a x)

  {-# minimal restrict | (#\) #-}

instance Restricted Void where
  (#\) _ = absurd

instance Restricted () where
  (#\) _ = id

instance Restricted Int where
  (#\) _ = id

instance Restricted Bool where
  (#\) _ = id

{-
instance Restricted a => Restricted (Map a) where

instance Restricted a => Restricted (Trie a) where

instance Restricted Permutation where
  a #\ p@Permutation (Tree (Trie l)) (Tree (Trie r)) = case Map.splitLookup a l of
    (_,Nothing,_) -> p
    (l, Just m, r) -> Permutation (Tree $ Trie $ Map.link (a+1) m l $ Map.mapKeysMonotonic (1+) r) 
                                 $ Tree $ Trie $ case Map.splitLookup a r of
      (l',Just m',r') -> Map.link (a+1) m' l' $ Map.mapKeysMonotonic (1+) r'
      (_,Nothing,_) -> error "Restricted(Permutation): illegal permutation"

instance Restricted Supp where
  a #\ s0@(Supp (Trie x)) = Supp $ Trie $ case Map.splitLookup a x of
    (_, Nothing, _) -> s0
    (l, Just m,  r) -> Map.link (a+1) m l (Map.mapKeysMonotonic (1+) r) -- TODO: use a shift-relative map

instance Restricted Set where
  a #\ s0@(Set (Trie x) = Set $ Trie $ case Map.splitLookup a x of
    (_, Nothing, _) -> s0
    (l, Just m,  r) -> Map.link (a+1) m l (Map.mapKeysMonotonic (1+) r) -- TODO: use a monoid-relative map
    

splitLookup :: Ord k => k -> Map k a -> (Map k a, Maybe a, Map k a)
-}

