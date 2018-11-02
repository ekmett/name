{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -funbox-strict-fields -fno-warn-orphans -fno-warn-type-defaults -O2 #-}
#ifdef ST_HACK
{-# OPTIONS_GHC -fno-full-laziness #-}
#endif

-- natural maps
module Patricia
  ( Map
  , singleton
  , empty
  , insert
  , lookup
  , delete
  , member
  , fromList
  , sup
  , traverseWithKey
  , unionWith
  , union
  , intersectionWith
  , intersection
  ) where

import Control.Applicative hiding (empty)
import Control.Monad (guard)
import Control.Monad.Zip
-- import Control.DeepSeq
import Control.Monad.ST hiding (runST)
import Data.Bits
import Data.Primitive.SmallArray
import Data.Foldable
import Data.Functor
import Data.Monoid
import Data.Traversable hiding (for)
import Data.Word
import Numeric.Natural
import GHC.Integer.Logarithms
import Data.Int
import qualified GHC.Exts as Exts
import Prelude hiding (lookup, length, foldr)
import GHC.Types
import GHC.ST

type Key = Natural
type Mask = Word16
type Offset = Int

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)
{-# inlineable ptrEq #-}

ptrNeq :: a -> a -> Bool
ptrNeq x y = isTrue# (Exts.reallyUnsafePtrEquality# x y Exts./=# 1#)
{-# inlineable ptrNeq #-}

data Map v
  = Full !Key !Offset !(SmallArray (Map v))
  | Node !Key !Offset !Mask !(SmallArray (Map v))
  | Tip  !Key v
  | Nil
  deriving Show

node :: Key -> Offset -> Mask -> SmallArray (Map v) -> Map v
node k o 0xffff a = Full k o a
node k o m a      = Node k o m a
{-# inline node #-}

small :: Key -> Offset -> Mask -> SmallArray (Map v) -> Map v
small k o 0xffff a = Full k o a
small k o m a = case compare (length a) 1 of
  LT -> Nil
  EQ -> indexSmallArray a 0 
  GT -> Node k o m a
{-# inline small #-}

-- find the largest key contained in this map
sup :: Map v -> Maybe Natural
sup Nil = Nothing
sup (Tip k _) = Just k
sup (Node _ _ m a) = indexSmallArrayM a (popCount m - 1) >>= sup
sup (Full _ _ a) = indexSmallArrayM a 15 >>= sup

-- instance NFData v => NFData (Map v) where
--  rnf (Full _ _ a)   = rnf a
--  rnf (Node _ _ _ a) = rnf a
--  rnf (Tip _ v) = rnf v
--  rnf Nil = ()

instance Functor Map where
  fmap f = go where
    go (Full k o a) = Full k o (fmap go a)
    go (Node k o m a) = Node k o m (fmap go a)
    go (Tip k v) = Tip k (f v)
    go Nil = Nil
  {-# inlineable fmap #-}

instance Foldable Map where
  foldMap f = go where
    go (Full _ _ a) = foldMap go a
    go (Node _ _ _ a) = foldMap go a
    go (Tip _ v) = f v
    go Nil = mempty
  {-# inlineable foldMap #-}

instance Traversable Map where
  traverse f = go where
    go (Full k o a) = Full k o <$> traverse go a
    go (Node k o m a) = Node k o m <$> traverse go a
    go (Tip k v) = Tip k <$> f v
    go Nil = pure Nil
  {-# inlineable traverse #-}

traverseWithKey :: Applicative f => (Natural -> a -> f b) -> Map a -> f (Map b)
traverseWithKey f = go where
  go (Full k o a) = Full k o <$> traverse go a
  go (Node k o m a) = Node k o m <$> traverse go a
  go (Tip k v) = Tip k <$> f k v
  go Nil = pure Nil

log2 :: Key -> Int
log2 n = I# (integerLog2# (toInteger n))
{-# inline log2 #-}

-- Note: 'level 0' will return a negative shift, don't use it
level :: Key -> Int
level w = log2 w .&. complement 0x3
{-# inline level #-}

maskBit :: Key -> Offset -> Int
maskBit k o = fromIntegral (unsafeShiftR k o .&. 0xf)
{-# inline maskBit #-}

mask :: Key -> Offset -> Word16
mask k o = bit (maskBit k o)
{-# inline mask #-}

start :: Int -> Key -> Key
start o k = fromInteger (toInteger k .&. unsafeShiftL (-1) (o+4))

-- offset :: Int -> Word16 -> Int
-- offset k w = popCount $ w .&. (bit k - 1)
-- {-# inline offset #-}

fork :: Int -> Key -> Map v -> Key -> Map v -> Map v
fork o k n ok on = Node (start o k) o (mask k o .|. mask ok o) $ runST $ do
  arr <- newSmallArray 2 n
  writeSmallArray arr (fromEnum (k < ok)) on
  unsafeFreezeSmallArray arr

insert :: Key -> v -> Map v -> Map v
insert !k v xs0 = go xs0 where
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

for :: (Num a, Ord a, Applicative m) => a -> a -> (a -> m ()) -> m ()
for s e f = if s <= e then go s else pure () where
  go !x
    | x == e    = f x
    | otherwise = f x *> go (x+1)

instance Semigroup a => Semigroup (Map a) where
  (<>) = unionWith (<>)

instance Semigroup a => Monoid (Map a) where
  mempty = Nil

unionWith :: (v -> v -> v) -> Map v -> Map v -> Map v
unionWith f = go where
  go Nil r = r
  go l Nil = l
  go nn@(Tip k v) on@(Tip ok ov) 
    | k /= ok       = fork (level (xor ok k)) k nn ok on
    | !uv <- f v ov = if ptrEq v uv then nn else Tip k uv
  go nn@(Tip k _) on@(Node ok n m as)
    | wd > 0xf = fork (level okk) k nn ok on
    | m .&. b == 0 = node ok n (m .|. b) (insertSmallArray odm nn as)
    | !oz <- indexSmallArray as odm, !z <- go nn oz, ptrNeq z oz = Node ok n m (updateSmallArray odm z as)
    | otherwise = on -- no changes
    where
      okk = xor ok k
      wd  = unsafeShiftR okk n
      d   = fromIntegral wd
      b   = bit d
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
      d   = fromIntegral wd
      b   = bit d
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
    | !ua <- mzipWith go la ra = maybe (Full lk ln ua) (const l) $ for 0 15 $ \i -> do
      x <- indexSmallArrayM la i
      y <- indexSmallArrayM ua i
      guard $ ptrEq x y
    where
      okk = xor lk rk
      wd = unsafeShiftR okk (min ln rn)
  go l@(Full lk ln la) r@(Node rk rn rm ra)
    | wd > 0xf = fork (level okk) lk l rk r
    | !ua <- mapSmallArrayWithIndex tweak la = maybe (Full lk ln ua) (const l) $ for 0 15 $ \i -> do
      x <- indexSmallArrayM la i
      y <- indexSmallArrayM ua i
      guard $ ptrEq x y
    where
      okk = xor lk rk
      wd = unsafeShiftR okk (min ln rn)
      tweak d lx 
        | rm .&. b == 0 = lx -- missing on right
        | otherwise = go lx $ indexSmallArray ra $ popCount $ rm .&. (b - 1)
        where b = bit d
  go l@(Node lk ln lm la) r@(Full rk rn ra) 
    | wd > 0xf = fork (level okk) lk l rk r
    | !ua <- mapSmallArrayWithIndex tweak ra = maybe (Full rk rn ua) (const r) $ for 0 15 $ \i -> do
       x <- indexSmallArrayM la i
       y <- indexSmallArrayM ua i
       guard $ ptrEq x y
    where
       okk = xor lk rk
       wd = unsafeShiftR okk (min ln rn)
       tweak d rx 
         | lm .&. b == 0 = rx -- missing on right
         | otherwise = go (indexSmallArray la $ popCount $ lm .&. (b-1)) rx
         where b = bit d
  go l@(Node lk ln lm la) r@(Node rk rn rm ra) 
    | wd > 0xf = fork (level okk) lk l rk r
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
       wd = unsafeShiftR okk (min ln rn)
        
union :: Map v -> Map v -> Map v
union = unionWith const
{-# inline union #-}

intersection :: Map v -> Map v -> Map v
intersection = intersectionWith const
{-# inline intersection #-}

-- segfaults
intersectionWith :: (a -> b -> c) -> Map a -> Map b -> Map c
intersectionWith f = go where 
  go Nil _ = Nil
  go _ Nil = Nil
  go (Tip lk lv) r = case lookup lk r of
    Nothing -> Nil
    Just rv -> Tip lk (f lv rv)
  go l (Tip rk rv) = case lookup rk l of
    Nothing -> Nil
    Just lv -> Tip rk (f lv rv)
  go l@(Node lk ln lm la) r@(Node rk rn rm ra) = gon l lk ln lm     la r rk rn rm     ra
  go l@(Full lk ln la) r@(Node rk rn rm ra)    = gon l lk ln 0xffff la r rk rn rm     ra
  go l@(Node lk ln lm la) r@(Full rk rn ra)    = gon l lk ln lm     la r rk rn 0xffff ra
  go l@(Full lk ln la) r@(Full rk rn ra)       = gon l lk ln 0xffff la r rk rn 0xffff ra
  gon l lk ln lm la r rk rn rm ra 
    | unsafeShiftR (xor lk rk) (max ln rn) /= 0 = Nil -- disjoint
    | otherwise = case compare ln rn of 
      LT -> go l (trim lk ln r) -- containment
      GT -> go (trim rk rn l) r -- containment
      EQ -> runST $ do
        let cm0 = lm .|. rm
            cmp = popCount cm0
        cma <- newSmallArray cmp undefined
        let loop 0 !i um = pure (i,um)
            loop cm i um = do
              let !d = countTrailingZeros cm
                  !b = bit d
                  !li = popCount $ lm .&. (b-1)
                  !ri = popCount $ rm .&. (b-1)
              lx <- indexSmallArrayM la li
              rx <- indexSmallArrayM ra ri
              case go lx rx of
                Nil -> loop (cm .&. complement b) i um -- dropped
                ux -> do
                  writeSmallArray cma i ux
                  loop (cm .&. complement b) (i+1) (um .|. b)
        (j,um) <- loop cm0 0 0
        if um == cm0 then small lk ln um <$> unsafeFreezeSmallArray cma  
                     else small lk ln um <$> freezeSmallArray cma 0 j -- take the first ump of the elements
{-# inlineable intersectionWith #-}

delete :: Key -> Map v -> Map v
delete !k xs0 = go xs0 where
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
        | m' .&. (m'-1) == 0 -> indexSmallArray as (complementBit odm 0) -- we're down to one thing in the mask, delete the Node
        | otherwise          -> Node ok n m' (deleteSmallArray odm as) -- deleting one node from a mask with 3+ entries
      _   -> Node ok n m (updateSmallArray odm z as)
    | otherwise = on
    where
      okk = xor ok k
      wd = unsafeShiftR okk n
      d = fromIntegral wd
      b = bit d
      odm = popCount $ m .&. (b - 1)
      m' = m .&. complement b
  go on@(Tip ok _) 
    | k /= ok = on
    | otherwise = Nil
  go Nil = Nil

lookup :: Key -> Map v -> Maybe v
lookup !k (Full ok o a)
  | z <- unsafeShiftR (xor k ok) o, z <= 0xf = lookup k $ indexSmallArray a (fromIntegral z)
  | otherwise = Nothing
lookup k (Node ok o m a)
  | z <= 0xf && m .&. b /= 0 = lookup k $ indexSmallArray a $ popCount $ m .&. (b - 1)
  | otherwise = Nothing
  where
    z = unsafeShiftR (xor k ok) o
    b = bit (fromIntegral z)
lookup k (Tip ok ov)
  | k == ok   = Just ov
  | otherwise = Nothing
lookup _ Nil = Nothing
{-# inlineable lookup #-}

-- trim k 0 should always yield either a Tip or a Nil
trim :: Key -> Offset -> Map a -> Map a
trim _ _ Nil = Nil
trim k n on@(Tip ok _)
  | unsafeShiftR okk n <= 0xf = on -- keep if in cone -- use 0?
  | otherwise                 = Nil
  where okk = xor k ok
trim k n on@(Node rk rn rm ra)
  | unsafeShiftR okk (max n rn) /= 0 = Nil
  | n <= rn = on
  | b .&. rm == 0 = Nil
  | otherwise = trim k n $ indexSmallArray ra $ popCount $ rm .&. (b-1)
  where
    okk = xor k rk
    z = unsafeShiftR okk rn
    b = bit (fromIntegral z)
trim k n on@(Full rk rn ra)
  | unsafeShiftR okk (max n rn) /= 0 = Nil
  | n <= rn = on
  | otherwise = trim k n $ indexSmallArray ra $ fromIntegral z
  where
    okk = xor k rk
    z = unsafeShiftR okk rn
{-# inlineable trim #-}


member :: Key -> Map v -> Bool
member !k (Full ok o a)
  | z <- unsafeShiftR (xor k ok) o = z <= 0xf && member k (indexSmallArray a (fromIntegral z))
member k (Node ok o m a)
  | z <- unsafeShiftR (xor k ok) o
  = z <= 0xf && let b = bit (fromIntegral z) in
    m .&. b /= 0 && member k (indexSmallArray a (popCount (m .&. (b - 1))))
member k (Tip ok _) = k == ok
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
  o <- clone16 i
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

clone16 :: SmallArray a -> ST s (SmallMutableArray s a)
clone16 i = do
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
{-# inline clone16 #-}

mapSmallArrayWithIndex :: forall a b. (Int -> a -> b) -> SmallArray a -> SmallArray b
mapSmallArrayWithIndex f i = runST $ do
  let n = length i
  o <- newSmallArray n (undefined :: b)
  for 0 (n-1) $ \k -> do
     x <- indexSmallArrayM i k 
     writeSmallArray o k $! f k x
  unsafeFreezeSmallArray o
{-# inline mapSmallArrayWithIndex #-}


-- | Build a singleton Map
singleton :: Key -> v -> Map v
singleton !k v = Tip k v
{-# inline singleton #-}

fromList :: [(Key,v)] -> Map v
fromList xs = foldl' (\r (k,v) -> insert k v r) Nil xs
{-# inline fromList #-}

empty :: Map a
empty = Nil
{-# inline empty #-}
