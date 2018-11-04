{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall -funbox-strict-fields -fno-warn-orphans -fno-warn-type-defaults -O2 #-}
#ifdef ST_HACK
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif

-- natural maps
module Nominal.Internal.Trie
{-
  ( Trie
  , singleton
  , empty
  , insert
  , lookup
  , delete
  , member
  , fromList
  , sup
  , unionWith
  , union
  , intersectionWith
  , intersection
  , diff
  ) -} where

import Control.Applicative hiding (empty)
import Control.Lens
import Control.Monad
import Control.Monad.Zip
import Control.Monad.ST hiding (runST)
import Data.Bits
import Data.Foldable
import Data.Functor.Bind
import Data.Int
import Data.Maybe
import Data.Monoid
import Data.Primitive.SmallArray
import Data.Word
import qualified GHC.Exts as Exts
import GHC.Integer.Logarithms
import GHC.ST
import GHC.Types
import Numeric.Natural
import Prelude hiding (lookup, length, foldr)

newtype Atom = A Natural deriving (Eq,Num) -- Num only for convenience
instance Show Atom where
  showsPrec d (A n) = showsPrec d n

type Mask = Word16
type Offset = Int

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
{-# inlineable ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts./=# 1#)
{-# inlineable ptrNeq #-}

-- a nybble-based patricia trie mapping Naturals to values
data Trie v
  = Full !Natural !Offset !(SmallArray (Trie v))
  | Node !Natural !Offset !Mask !(SmallArray (Trie v))
  | Tip  !Natural v
  | Nil
  deriving Show

-- valid :: Trie v -> Bool
-- valid Nil = True
-- valid Tip{} = True
-- valid (Node n o m a) = all (iall (\j _ -> unsafeShiftR (xor j n) == 0)) as -- <= 0xf?

{-# COMPLETE Full, Node, Tip, Nil #-}
{-# COMPLETE NODE, Tip, Nil #-}

instance Eq a => Eq (Trie a) where
  xs == ys = itoList xs == itoList ys

instance Ord a => Ord (Trie a) where
  compare xs ys = tweak xs `compare` tweak ys where
    tweak = ifoldr (\(A i) a r -> (i,a):r) []

asNode :: Trie v -> Maybe (Natural, Offset, Mask, SmallArray (Trie v))
asNode Nil = Nothing
asNode (Tip _ _) = Nothing
asNode (Node k o m a) = Just (k,o,m,a)
asNode (Full k o a) = Just (k,o,0xffff,a)

pattern NODE :: Natural -> Offset -> Mask -> SmallArray (Trie v) -> Trie v
pattern NODE k o m a <- (asNode -> Just (k,o,m,a)) where
  NODE k o m a = node k o m a

node :: Natural -> Offset -> Mask -> SmallArray (Trie v) -> Trie v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# inline node #-}

small :: Natural -> Offset -> Mask -> SmallArray (Trie v) -> Trie v
small k o 0xffff a = Full k o a
small k o m a = case compare (length a) 1 of
  LT -> Nil
  EQ -> indexSmallArray a 0 
  GT -> Node k o m a
{-# inline small #-}

-- find the largest key contained in this map
sup :: Trie v -> Maybe Atom
sup Nil = Nothing
sup (Tip k _) = Just (A k)
sup (Node _ _ m a) = indexSmallArrayM a (popCount m - 1) >>= sup
sup (Full _ _ a) = indexSmallArrayM a 15 >>= sup

-- reduced to a single bit
single :: Word16 -> Bool
single m = m .&. (m-1) == 0
{-# inline single #-}

instance Functor Trie where
  fmap f = go where
    go (Full k o a) = Full k o (fmap go a)
    go (Node k o m a) = Node k o m (fmap go a)
    go (Tip k v) = Tip k (f v)
    go Nil = Nil
  {-# inline fmap #-}

instance Foldable Trie where
  foldMap f = go where
    go (Full _ _ a) = foldMap go a
    go (Node _ _ _ a) = foldMap go a
    go (Tip _ v) = f v
    go Nil = mempty
  {-# inline foldMap #-}

instance Traversable Trie where
  traverse f = go where
    go (Full k o a) = Full k o <$> traverse go a
    go (Node k o m a) = Node k o m <$> traverse go a
    go (Tip k v) = Tip k <$> f v
    go Nil = pure Nil
  {-# inline traverse #-}

instance FunctorWithIndex Atom Trie where
  imap f = go where
    go (Full k o a) = Full k o (fmap go a)
    go (Node k o m a) = Node k o m (fmap go a)
    go (Tip k v) = Tip k (f (A k) v)
    go Nil = Nil
  {-# inline imap #-}

instance FoldableWithIndex Atom Trie where
  ifoldMap f = go where
    go (Full _ _ a) = foldMap go a
    go (Node _ _ _ a) = foldMap go a
    go (Tip k v) = f (A k) v
    go Nil = mempty

instance TraversableWithIndex Atom Trie where
  itraverse f = go where
    go (Full k o a) = Full k o <$> traverse go a
    go (Node k o m a) = Node k o m <$> traverse go a
    go (Tip k v) = Tip k <$> f (A k) v
    go Nil = pure Nil
  {-# inline itraverse #-}

instance Apply Trie where
  liftF2 = intersectionWith

instance Bind Trie where
  m >>- f = ifilterMap (\i -> lookup i . f) m

log2 :: Natural -> Int
log2 n = I# (integerLog2# (toInteger n))
{-# inline log2 #-}

-- Note: 'level 0' will return a negative shift, don't use it
level :: Natural -> Int
level w = log2 w .&. complement 0x3
{-# inline level #-}

maskBit :: Natural -> Offset -> Int
maskBit k o = fromIntegral (unsafeShiftR k o .&. 0xf)
{-# inline maskBit #-}

mask :: Natural -> Offset -> Word16
mask k o = bit (maskBit k o)
{-# inline mask #-}

start :: Int -> Natural -> Natural
start o k = fromInteger (toInteger k .&. unsafeShiftL (-1) (o+4))

-- offset :: Int -> Word16 -> Int
-- offset k w = popCount $ w .&. (bit k - 1)
-- {-# inline offset #-}

forkx :: Int -> Natural -> Trie v -> Natural -> Trie v -> Trie v
forkx _ _ Nil _ r = r
forkx _ _ l _ Nil = l
forkx o k n ok on = fork o k n ok on

fork :: Int -> Natural -> Trie v -> Natural -> Trie v -> Trie v
fork o k n ok on = Node (start o k) o (mask k o .|. mask ok o) $ runST $ do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  unsafeFreezeSmallArray arr

insert :: Atom -> v -> Trie v -> Trie v
insert !(A k) v xs0 = go xs0 where
  go on@(Full ok n as)
    | wd > 0xf = fork (level okk) k (Tip k v) ok on
    | !oz <- indexSmallArray as d, !z <- go oz, ptrNeq z oz = Full ok n (update16 d z as)
    | otherwise = on
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
  go on@(Node ok n m as)
    | wd > 0xf = fork (level okk) k (Tip k v) ok on
    | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm (Tip k v) as)
    | !oz <- indexSmallArray as odm, !z <- go oz, ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
    | otherwise = on
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
      b   = bit d
      odm = popCount $ m .&. (b - 1)
  go on@(Tip ok ov)
    | k /= ok    = fork (level (xor ok k)) k (Tip k v) ok on
    | ptrEq v ov = on
    | otherwise  = Tip k v
  go Nil = Tip k v
{-# inlineable insert #-}

for :: Applicative m => Int -> Int -> (Int -> m ()) -> m ()
for s e f = go s where
  go !x
    | x < e     = f x *> go (x+1)
    | otherwise = pure ()
{-# inline for #-}

instance Semigroup a => Semigroup (Trie a) where
  (<>) = unionWith (<>)
  {-# inlineable (<>) #-}

instance Semigroup a => Monoid (Trie a) where
  mempty = Nil
  {-# inline mempty #-}

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith = unionWithKey . const
{-# inline unionWith #-}

data These a b = This a | That b | These a b

meld :: (Atom -> These a b -> Maybe c) -> Trie a -> Trie b -> Trie c
meld f a b = ifilterMap f $ unionWith (\(This x) (That y) -> These x y) (This <$> a) (That <$> b)

{-
meld flr fl fr = go where
  go Nil Nil = Nil
  go Nil r = ifilterMap fr r
  go l Nil = ifilterMap fl l
  go l@(Tip lk lv) r@(Tip rk rv)
    | lk == rk  = case flr (A lk) lv rv of
      Nothing -> Nil
      Just c -> Tip lk c
    | otherwise = forkx (level (xor lk rk)) lk (ifilterMap fl l) rk (ifilterMap fr r)
  go l@(Tip lk lv) r@(NODE rk rn rm ra)
    | wd > 0xf = forkx (level okk) lk (ifilterMap fl l) rk (ifilterMap fr r)
    | rm .&. b == 0 = case ifilterMap fl l of
      Nil -> ifilterMap fr r
      z   -> node rk rn (rm .|. b) (insertSmallArray odm z ra)
    | otherwise = case go l (indexSmallArray as odm) of
      Nil -> small rk rn (rm .&. complement b) (deleteSmallArray odm ra)
      z   -> Node rk rn rm (updateSmallArray odm z as)
    where 
      okk = xor lk rk
      wd = unsafeShiftR okk rn
      b = bit (fromIntegral wd)
      odm = popCount $ rm .&. (b-1)
  ...
-}


unionWithKey :: (Atom -> a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWithKey f = go where
  go Nil r = r
  go l Nil = l
  go nn@(Tip k v) on@(Tip ok ov) 
    | k /= ok       = fork (level (xor ok k)) k nn ok on
    | !uv <- f (A k) v ov = if ptrEq v uv then nn else Tip k uv
  go nn@(Tip k _) on@(Node ok n m as)
    | wd > 0xf = fork (level okk) k nn ok on
    | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm nn as)
    | !oz <- indexSmallArray as odm, !z <- go nn oz, ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
    | otherwise = on -- no changes
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      b   = bit (fromIntegral wd)
      odm = popCount $ m .&. (b - 1)
  go nn@(Tip k _) on@(Full ok n as)
    | wd > 0xf = fork (level okk) k nn ok on
    | !oz <- indexSmallArray as d, !z <- go nn oz, ptrNeq z oz = Full ok n (update16 d z as)
    | otherwise = on
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
  go on@(Node ok n m as) nn@(Tip k _)
    | wd > 0xf = fork (level okk) k nn ok on
    | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm nn as)
    | !oz <- indexSmallArray as odm, !z <- go oz nn, ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
    | otherwise = on -- no changes
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      b   = bit (fromIntegral wd)
      odm = popCount $ m .&. (b - 1)
  go on@(Full ok n as) nn@(Tip k _)
    | wd > 0xf = fork (level okk) k nn ok on
    | !oz <- indexSmallArray as d, !z <- go oz nn, ptrNeq z oz = Full ok n (update16 d z as)
    | otherwise = on
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
  go l@(Full lk ln la) r@(Full rk rn ra)
    | wd > 0xf  = fork (level okk) lk l rk r
    | ln > rn = let zd = indexSmallArray la (fromIntegral wd)
                    z = go zd r
                in if ptrEq z zd then l
                                 else Full lk ln $ updateSmallArray (fromIntegral wd) z la
    | ln < rn = let zd = indexSmallArray ra (fromIntegral wd)
                    z = go l zd
                in if ptrEq z zd then r
                                 else Full rk rn $ updateSmallArray (fromIntegral wd) z ra
    | !ua <- mzipWith go la ra = maybe (Full lk ln ua) (const l) $ for 0 16 $ \i -> do
      x <- indexSmallArrayM la i
      y <- indexSmallArrayM ua i
      guard $ ptrEq x y
    where
      okk = xor lk rk
      wd = unsafeShiftR okk (max ln rn)
  go l@(Full lk ln la) r@(Node rk rn rm ra)
    | wd > 0xf = fork (level okk) lk l rk r
    | ln > rn = let zd = indexSmallArray la (fromIntegral wd)
                    z = go zd r
                in if ptrEq z zd then l
                                 else Full lk ln $ updateSmallArray (fromIntegral wd) z la
    | ln < rn = if rm .&. bd /= 0
        then let zd = indexSmallArray ra rdm
                 z = go l zd
             in if ptrEq z zd then r
                              else Node rk rn rm $ updateSmallArray rdm z ra
        else node rk rn (rm .|. bd) (insertSmallArray rdm l ra)
    | !ua <- mapSmallArrayWithIndex tweak la = maybe (Full lk ln ua) (const l) $ for 0 16 $ \i -> do
      x <- indexSmallArrayM la i
      y <- indexSmallArrayM ua i
      guard $ ptrEq x y
    where
      okk = xor lk rk
      wd = unsafeShiftR okk (max ln rn)
      bd = bit (fromIntegral wd)
      rdm = popCount $ rm .&. (bd - 1)
      tweak d lx 
        | rm .&. b == 0 = lx -- missing on right
        | otherwise = go lx $ indexSmallArray ra $ popCount $ rm .&. (b - 1)
        where b = bit d
  go l@(Node lk ln lm la) r@(Full rk rn ra) 
    | wd > 0xf = fork (level okk) lk l rk r
    | ln > rn = if lm .&. bd /= 0
        then let zd = indexSmallArray la ldm
                 z = go zd r
             in if ptrEq z zd then l
                              else Node lk ln lm $ updateSmallArray ldm z la
        else node lk ln (lm .|. bd) (insertSmallArray ldm r la)
    | ln < rn = let zd = indexSmallArray ra (fromIntegral wd)
                    z = go l zd
                in if ptrEq z zd then r
                                 else Full rk rn $ updateSmallArray (fromIntegral wd) z ra
    | !ua <- mapSmallArrayWithIndex tweak ra = maybe (Full rk rn ua) (const r) $ for 0 16 $ \i -> do
       x <- indexSmallArrayM la i
       y <- indexSmallArrayM ua i
       guard $ ptrEq x y
    where
       okk = xor lk rk
       wd = unsafeShiftR okk (max ln rn)
       bd = bit (fromIntegral wd)
       ldm = popCount $ lm .&. (bd - 1)
       tweak d rx 
         | lm .&. b == 0 = rx -- missing on right
         | otherwise = go (indexSmallArray la $ popCount $ lm .&. (b-1)) rx
         where b = bit d
  go l@(Node lk ln lm la) r@(Node rk rn rm ra)
    | wd > 0xf = fork (level okk) lk l rk r
    | ln > rn = if lm .&. bd /= 0
        then let zd = indexSmallArray la ldm
                 z = go zd r
             in if ptrEq z zd then l
                              else Node lk ln lm $ updateSmallArray ldm z la
        else node lk ln (lm .|. bd) (insertSmallArray ldm r la)
    | ln < rn = if rm .&. bd /= 0
        then let zd = indexSmallArray ra rdm
                 z = go l zd
             in if ptrEq z zd then r
                              else Node rk rn rm $ updateSmallArray rdm z ra
        else node rk rn (rm .|. bd) (insertSmallArray rdm l ra)
    | otherwise = runST $ do -- TODO: check sharing while we go
        let um = lm .|. rm
        uma <- newSmallArray (popCount um) undefined
        let loop 0 !_ acc = pure acc
            loop cm i acc = do
              let !d = countTrailingZeros cm
                  !b = bit d
                  !li = popCount $ lm .&. (b-1)
                  !ri = popCount $ rm .&. (b-1)
              same <- if
                | lm .&. b == 0 -> False <$ (indexSmallArrayM ra ri >>= writeSmallArray uma i)
                | rm .&. b == 0 -> True <$ (indexSmallArrayM la li >>= writeSmallArray uma i)
                | otherwise -> do
                  lx <- indexSmallArrayM la li
                  rx <- indexSmallArrayM ra ri
                  let !ux = go lx rx 
                  ptrEq lx ux <$ writeSmallArray uma i ux
              loop (cm .&. complement b) (i+1) (acc && same)
        same <- loop um 0 (lm == um)
        if same
          then pure l
          else node lk ln um <$> unsafeFreezeSmallArray uma
    where
       okk = xor lk rk
       wd = unsafeShiftR okk (max ln rn)
       bd = bit (fromIntegral wd)
       ldm = popCount $ lm .&. (bd - 1)
       rdm = popCount $ rm .&. (bd - 1)

union :: Trie a -> Trie a -> Trie a
union = unionWith const
{-# inline union #-}

intersection :: Trie a -> Trie a -> Trie a
intersection = intersectionWith const
{-# inline intersection #-}

-- segfaults
intersectionWith :: (a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWith = intersectionWithKey . const

intersectionWithKey :: (Atom -> a -> b -> c) -> Trie a -> Trie b -> Trie c
intersectionWithKey f = go where 
  go Nil _ = Nil
  go _ Nil = Nil
  go (Tip lk lv) r = case lookup (A lk) r of
    Nothing -> Nil
    Just rv -> Tip lk (f (A lk) lv rv)
  go l (Tip rk rv) = case lookup (A rk) l of
    Nothing -> Nil
    Just lv -> Tip rk (f (A rk) lv rv)
  go l@(Node lk ln lm la) r@(Node rk rn rm ra)
    | unsafeShiftR okk (min ln rn) > 0xf = Nil -- disjoint
    | otherwise = case compare ln rn of 
      LT | rb .&. rm == 0 -> Nil
      LT -> go l $ indexSmallArray ra $ popCount $ rm .&. (rb-1) -- lookup
      GT | lb .&. lm == 0 -> Nil -- contained, but disjoint
      GT -> go (indexSmallArray la $ popCount $ lm .&. (lb-1)) r -- lookup
      EQ -> runST $ do -- same level, merge
        let cm0 = lm .&. rm
        cma <- newSmallArray (popCount cm0) undefined
        let loop 0 !i !um = small lk ln um <$> if um == cm0
              then unsafeFreezeSmallArray cma -- all elements made it through
              else freezeSmallArray cma 0 i -- only take the first j elements
            loop cm i um = do
              let !b = bit (countTrailingZeros cm)
              lx <- indexSmallArrayM la $ popCount $ lm .&. (b-1)
              rx <- indexSmallArrayM ra $ popCount $ rm .&. (b-1)
              case go lx rx of
                Nil -> loop (cm .&. complement b) i um -- dropped
                ux -> writeSmallArray cma i ux >> loop (cm .&. complement b) (i+1) (um .|. b)
        loop cm0 0 0
    where
      okk = xor lk rk
      rb = bit (fromIntegral (unsafeShiftR okk rn))
      lb = bit (fromIntegral (unsafeShiftR okk ln))
  go l@(Full lk ln la) r@(Node rk rn rm ra)
    | unsafeShiftR okk (min ln rn) > 0xf = Nil -- disjoint
    | otherwise = case compare ln rn of 
      LT | rb .&. rm == 0 -> Nil
      LT -> go l $ indexSmallArray ra $ popCount $ rm .&. (rb-1)
      GT -> go (indexSmallArray la ld) r
      EQ -> runST $ do -- same level, merge
        cma <- newSmallArray (length ra) undefined
        let loop 0 !i !um = small lk ln um <$> if um == rm
              then unsafeFreezeSmallArray cma -- all elements made it through
              else freezeSmallArray cma 0 i -- only take the first j elements
            loop cm i um = do
              let !d = countTrailingZeros cm
                  !b = bit d
              lx <- indexSmallArrayM la d
              rx <- indexSmallArrayM ra $ popCount $ rm .&. (b-1)
              case go lx rx of
                Nil -> loop (cm .&. complement b) i um -- dropped
                ux -> writeSmallArray cma i ux >> loop (cm .&. complement b) (i+1) (um .|. b)
        loop rm 0 0
    where
      okk = xor lk rk
      rb = bit (fromIntegral (unsafeShiftR okk rn))
      ld = fromIntegral (unsafeShiftR okk ln)
  go l@(Node lk ln lm la) r@(Full rk rn ra)
    | unsafeShiftR okk (min ln rn) > 0xf = Nil -- disjoint
    | otherwise = case compare ln rn of 
      LT -> go l (indexSmallArray ra rd)
      GT | lb .&. lm == 0 -> Nil -- contained, but disjoint
      GT -> go (indexSmallArray la $ popCount $ lm .&. (lb-1)) r -- lookup
      EQ -> runST $ do -- same level, merge
        cma <- newSmallArray (length la) undefined
        let loop 0 !i !um = small lk ln um <$> if um == lm
              then unsafeFreezeSmallArray cma -- all elements made it through
              else freezeSmallArray cma 0 i -- only take the first j elements
            loop cm i um = do
              let !d = countTrailingZeros cm
                  !b = bit d
              lx <- indexSmallArrayM la $ popCount $ lm .&. (b-1) 
              rx <- indexSmallArrayM ra d
              case go lx rx of
                Nil -> loop (cm .&. complement b) i um -- dropped
                ux -> writeSmallArray cma i ux >> loop (cm .&. complement b) (i+1) (um .|. b)
        loop lm 0 0
    where
      okk = xor lk rk
      rd = fromIntegral (unsafeShiftR okk rn)
      lb = bit (fromIntegral (unsafeShiftR okk ln))
  go l@(Full lk ln la) r@(Full rk rn ra)
    | unsafeShiftR okk (min ln rn) > 0xf = Nil -- disjoint
    | otherwise = case compare ln rn of 
      LT -> go l (indexSmallArray ra rd)
      GT -> go (indexSmallArray la ld) r
      EQ -> runST $ do
        cma <- newSmallArray 16 undefined
        let loop 16 !i !um = small lk ln um <$> if um == 16
              then unsafeFreezeSmallArray cma
              else freezeSmallArray cma 0 i
            loop d i um = do
              let !b = bit d
              lx <- indexSmallArrayM la d
              rx <- indexSmallArrayM ra d
              case go lx rx of
                Nil -> loop (d+1) i um
                ux  -> writeSmallArray cma i ux >> loop (d+1) (i+1) (um .|. b)
        loop 0 0 0
    where okk = xor lk rk; rd = fromIntegral (unsafeShiftR okk rn); ld = fromIntegral (unsafeShiftR okk ln)
{-# inlineable intersectionWith #-}

filterMap :: (a -> Maybe b) -> Trie a -> Trie b
filterMap = ifilterMap . const
{-# inline filterMap #-}

ifilterMap :: (Atom -> a -> Maybe b) -> Trie a -> Trie b
ifilterMap f = go where
  go Nil = Nil
  go (Tip k v) = case f (A k) v of
    Nothing -> Nil
    Just u -> Tip k u
  go (Node ok on om oa) = runST $ do
    cma <- newSmallArray (length oa) undefined
    let loop 0 !i !um = small ok on um <$> if um == om
          then unsafeFreezeSmallArray cma
          else freezeSmallArray cma 0 i
        loop cm i um = do
          let !b = bit (countTrailingZeros cm)
          oz <- indexSmallArrayM oa $ popCount $ om .&. (b-1)
          case go oz of
            Nil -> loop (cm .&. complement b) i um
            z -> writeSmallArray cma i z >> loop (cm .&. complement b) (i+1) (um .|. b)
    loop om 0 0
  go (Full ok on oa) = runST $ do
    cma <- newSmallArray 16 undefined
    let loop 16 !i !um = small ok on um <$> if i == 16
          then unsafeFreezeSmallArray cma
          else freezeSmallArray cma 0 i
        loop d i um = do
          let !b = bit d
          oz <- indexSmallArrayM oa d 
          case go oz of
            Nil -> loop (d+1) i um
            z -> writeSmallArray cma i z >> loop (d+1) (i+1) (um .|. b)
    loop 0 0 0

filter :: (a -> Bool) -> Trie a -> Trie a
filter = ifilter . const
{-# inline filter #-}

ifilter :: (Atom -> a -> Bool) -> Trie a -> Trie a
ifilter p = go where
  go Nil = Nil
  go l@(Tip k v)
    | p (A k) v = l
    | otherwise = Nil
  go l@(Node ok on om oa) = runST $ do
    cma <- newSmallArray (length oa) undefined
    let loop 0 !i !um acc 
          | acc = pure l
          | otherwise = small ok on um <$> if um == om
          then unsafeFreezeSmallArray cma
          else freezeSmallArray cma 0 i
        loop cm i um acc = do
          let !b = bit (countTrailingZeros cm)
          oz <- indexSmallArrayM oa $ popCount $ om .&. (b-1)
          case go oz of
            Nil -> loop (cm .&. complement b) i um False
            z -> writeSmallArray cma i z >> loop (cm .&. complement b) (i+1) (um .|. b) (acc && ptrEq z oz)
    loop om 0 0 True
  go l@(Full ok on oa) = runST $ do
    cma <- newSmallArray 16 undefined
    let loop 16 !i !um acc 
          | acc = pure l
          | otherwise = small ok on um <$> if i == 16
          then unsafeFreezeSmallArray cma
          else freezeSmallArray cma 0 i
        loop d i um acc = do
          let !b = bit d
          oz <- indexSmallArrayM oa d 
          case go oz of
            Nil -> loop (d+1) i um False
            z -> writeSmallArray cma i z >> loop (d+1) (i+1) (um .|. b) (acc && ptrEq z oz)
    loop 0 0 0 True

diff :: Trie a -> Trie b -> Trie a
diff t Nil = t
diff Nil _ = Nil
diff l (Tip k _) = delete (A k) l
diff l@(Tip lk _) r = maybe l (const Nil) $ lookup (A lk) r
diff l@(NODE lk ln lm la) r@(NODE rk rn rm ra) = case compare ln rn of
    EQ | lm .&. rm == 0 -> l
    EQ -> runST $ do
      cma <- newSmallArray (length la) undefined
      let loop 0 !i !um = small lk ln um <$> if um == lm 
            then unsafeFreezeSmallArray cma
            else freezeSmallArray cma 0 i
          loop cm i um = do
            let !d = countTrailingZeros cm; !b = bit d
            x <- indexSmallArrayM la $ popCount $ lm .&. (b-1)
            if rm .&. b == 0
              then do
                writeSmallArray cma i x
                loop (cm .&. complement b) (i+1) (um .|. b)
              else do
                y <- indexSmallArrayM ra $ popCount $ rm .&. (b-1)
                case diff x y of
                  Nil -> loop (cm .&. complement b) i um
                  z -> writeSmallArray cma i z >> loop (cm .&. complement b) (i+1) (um .|. b)
      loop lm 0 0 
    LT | rm .&. rb == 0 -> l
    LT -> diff l $ indexSmallArray ra $ popCount $ rm .&. (rb - 1) -- otherwise
    GT | lm .&. lb == 0 -> l
       | !oz <- indexSmallArray la li, !z <- diff oz r, ptrNeq z oz -> case z of
         Nil
           | single lm' -> indexSmallArray la (complementBit li 0) -- we're down to one thing in the mask, remove Node
           | otherwise  -> Node lk ln lm' (deleteSmallArray li la) -- deleting one node from a mask with 3+ entries
         _ -> Node lk ln lm (updateSmallArray li z la)
       | otherwise -> l -- we overlapped, but nothing changed
      where
        li = popCount $ lm .&. (lb - 1)
        lm' = lm .&. complement lb
  where
    okk = xor lk rk
    rd = fromIntegral (unsafeShiftR okk rn)
    rb = bit rd
    ld = fromIntegral (unsafeShiftR okk ln)
    lb = bit ld
  
delete :: Atom -> Trie v -> Trie v
delete !(A k) xs0 = go xs0 where
  go on@(Full ok n as)
    | wd > 0xf = on
    | !oz <- indexSmallArray as d, !z <- go oz, ptrNeq z oz = case z of 
       Nil -> Node ok n (complement b) (deleteSmallArray d as)
       _   -> Full ok n (update16 d z as)
    | otherwise = on
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
      b   = bit d
  go on@(Node ok n m as) 
    | wd > 0xf     = on -- above us
    | m .&. b == 0 = on -- not present in this node
    | !oz <- indexSmallArray as odm, !z <- go oz, ptrNeq z oz = case z of
      Nil 
        | single m' -> indexSmallArray as (complementBit odm 0) -- we're down to one thing in the mask, delete the Node
        | otherwise -> Node ok n m' (deleteSmallArray odm as) -- deleting one node from a mask with 3+ entries
      _   -> Node ok n m (updateSmallArray odm z as)
    | otherwise = on
    where
      okk = xor ok k
      wd = unsafeShiftR okk n
      b = bit (fromIntegral wd)
      odm = popCount $ m .&. (b - 1)
      m' = m .&. complement b
  go on@(Tip ok _) 
    | k /= ok = on
    | otherwise = Nil
  go Nil = Nil

(!) :: Trie v -> Atom -> v
(!) t a = fromMaybe (error "Trie.!: missing atom") $ lookup a t

lookup :: Atom -> Trie v -> Maybe v
lookup !ak@(A k) (Full ok o a)
  | z <- unsafeShiftR (xor k ok) o, z <= 0xf = lookup ak $ indexSmallArray a (fromIntegral z)
  | otherwise = Nothing
lookup ak@(A k) (Node ok o m a)
  | z <= 0xf, m .&. b /= 0 = lookup ak $ indexSmallArray a $ popCount $ m .&. (b - 1)
  | otherwise = Nothing
  where z = unsafeShiftR (xor k ok) o; b = bit (fromIntegral z)
lookup (A k) (Tip ok ov)
  | k == ok   = Just ov
  | otherwise = Nothing
lookup _ Nil = Nothing
{-# inlineable lookup #-}

member :: Atom -> Trie v -> Bool
member !ak@(A k) (Full ok o a)
  | z <- unsafeShiftR (xor k ok) o = z <= 0xf && member ak (indexSmallArray a (fromIntegral z))
member ak@(A k) (Node ok o m a)
  | z <- unsafeShiftR (xor k ok) o
  = z <= 0xf && let b = bit (fromIntegral z) in
    m .&. b /= 0 && member ak (indexSmallArray a (popCount (m .&. (b - 1))))
member (A k) (Tip ok _) = k == ok
member _ Nil = False
{-# inlineable member #-}

updateSmallArray :: Int -> a -> SmallArray a -> SmallArray a
updateSmallArray !k a i = runST $ do
  let n = length i
  o <- newSmallArray n undefined
  copySmallArray o 0 i 0 n
  writeSmallArray o k a
  unsafeFreezeSmallArray o
{-# inlineable updateSmallArray #-}

update16 :: Int -> a -> SmallArray a -> SmallArray a
update16 !k a i = runST $ do
  o <- thaw16 i
  writeSmallArray o k a
  unsafeFreezeSmallArray o
{-# inlineable update16 #-}

insertSmallArray :: Int -> a -> SmallArray a -> SmallArray a
insertSmallArray !k a i = runST $ do
  let n = length i
  o <- newSmallArray (n + 1) a
  copySmallArray  o 0 i 0 k
  copySmallArray  o (k+1) i k (n-k)
  unsafeFreezeSmallArray o
{-# inlineable insertSmallArray #-}

deleteSmallArray :: Int -> SmallArray a -> SmallArray a
deleteSmallArray !k i = runST $ do
  let n = length i
  o <- newSmallArray (n - 1) undefined
  copySmallArray  o 0 i 0 k
  copySmallArray  o k i (k+1) (n-k-1)
  unsafeFreezeSmallArray o
{-# inlineable deleteSmallArray #-}

thaw16 :: SmallArray a -> ST s (SmallMutableArray s a)
thaw16 i = do
  o <- newSmallArray 16 undefined
  indexSmallArrayM i 0 >>= writeSmallArray o 0
  indexSmallArrayM i 1 >>= writeSmallArray o 1
  indexSmallArrayM i 2 >>= writeSmallArray o 2
  indexSmallArrayM i 3 >>= writeSmallArray o 3
  indexSmallArrayM i 4 >>= writeSmallArray o 4
  indexSmallArrayM i 5 >>= writeSmallArray o 5
  indexSmallArrayM i 6 >>= writeSmallArray o 6
  indexSmallArrayM i 7 >>= writeSmallArray o 7
  indexSmallArrayM i 8 >>= writeSmallArray o 8
  indexSmallArrayM i 9 >>= writeSmallArray o 9
  indexSmallArrayM i 10 >>= writeSmallArray o 10
  indexSmallArrayM i 11 >>= writeSmallArray o 11
  indexSmallArrayM i 12 >>= writeSmallArray o 12
  indexSmallArrayM i 13 >>= writeSmallArray o 13
  indexSmallArrayM i 14 >>= writeSmallArray o 14
  indexSmallArrayM i 15 >>= writeSmallArray o 15
  return o
{-# inline thaw16 #-}

mapSmallArrayWithIndex :: forall a b. (Int -> a -> b) -> SmallArray a -> SmallArray b
mapSmallArrayWithIndex f i = runST $ do
  let n = length i
  o <- newSmallArray n (undefined :: b)
  for 0 n $ \k -> do
    x <- indexSmallArrayM i k 
    writeSmallArray o k $! f k x
  unsafeFreezeSmallArray o
{-# inline mapSmallArrayWithIndex #-}

-- | Build a singleton Trie
singleton :: Atom -> v -> Trie v
singleton !(A k) v = Tip k v
{-# inline singleton #-}

fromList :: [(Atom,v)] -> Trie v
fromList xs = foldl' (\r (k,v) -> insert k v r) Nil xs
{-# inline fromList #-}

empty :: Trie a
empty = Nil
{-# inline empty #-}

type instance Index (Trie a) = Atom
type instance IxValue (Trie a) = a
instance Ixed (Trie a)
instance At (Trie a) where
  at i f m = f (lookup i m) <&> \case
    Nothing -> delete i m
    Just a -> insert i a m

{-
newtype Set = Set (Trie ())
data Permutation = Permutation (Trie Atom) (Trie Atom)
data Support where
  Supp :: Eq v => Trie v -> Support

data Predicate = Finite Set | Cofinite Set

data Map a = Map Support (Trie a) -- memoized approximate support

class Permutable t where 
  perm :: Permutation -> t -> t

class Permutable t => Nominal t where
  supp :: t -> Support

instance Nominal Permutation where supp (Perm t _) = Supp t
instance Nominal Support where supp = id
instance Nominal Atom where supp (A n) = Supp (singleton n)
instance Nominal (Map a) where supp (Map s _) = s
instance Nominal Set where supp (Set t) = Supp t
instance Nominal Predicate where supp (Finite t) = supp t; supp (Cofinite t) = supp t

data Perm a b where
  Perm :: (Permutable a, Permutable b) => (a -> b) -> Perm a b

data Nom a b where
  Nom :: (Nominal a, Nominal b) => Support -> (a -> b) -> Nom a b

class DistributiveLattice t where
  (/\), (\/) :: t -> t -> t
  bottom :: t

instance DistributiveLattice Support
instance DistributiveLattice Set
instance DistributiveLattice Predicate

class DistributiveLattice t => GBA t where
  (\\) :: t -> t -> t

instance GBA Set
instance GBA Predicate
-}
