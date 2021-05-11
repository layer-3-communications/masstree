{-# language BangPatterns #-}

module Data.Masstree.Utils where

import Prelude hiding (splitAt)
-- FIXME merge these utilities upstream where it makes sense
-- then use anmed imports
import Data.Primitive.Contiguous
import Data.Primitive (Prim)

import Control.Monad.ST (runST)
import Control.Monad.ST.Run (runSmallArrayST,runPrimArrayST)

checkedIndex :: (Contiguous arr, Element arr a) => arr a -> Int -> Maybe a
{-# inline checkedIndex #-}
checkedIndex xs i
  | i < size xs = Just $ index xs i
  | otherwise = Nothing

-- insert element so that it becomes the new element at the given index
-- the preceding elements remain unchanged, and the successding element
-- indexes are shifted over
smallInsertAt :: SmallArray a -> Int -> a -> SmallArray a
smallInsertAt !src !i !x = runSmallArrayST $ do
  let len0 = size src
  dst <- replicateMutable (len0 + 1) x
  copy dst 0 src 0 i
  copy dst (i + 1) src i (len0 - i)
  unsafeFreeze dst

-- Copy of smallInsertAt. PrimArray can skip the memset the SmallArray
-- must endure.
primInsertAt :: Prim a => PrimArray a -> Int -> a -> PrimArray a
{-# inline primInsertAt #-}
primInsertAt !src !i !x = runPrimArrayST $ do
  let len0 = size src
  dst <- new (len0 + 1)
  write dst i x
  copy dst 0 src 0 i
  copy dst (i + 1) src i (len0 - i)
  unsafeFreeze dst

-- split the given array at the given index (so that the length of the first
-- is equal to the given index)
splitAt :: (Contiguous arr, Element arr a) => arr a -> Int -> (arr a, arr a)
{-# inline splitAt #-}
splitAt src lenL =
  let lenR = size src - lenL
   in (clone src 0 lenL, clone src lenL lenR)

-- insert an element into an array, then split it
-- performs less copying than using `insertAt` and `splitAt` separately
insertAtThenSplitAt :: (Contiguous arr, Element arr a)
  => arr a -> Int -> a -> Int -> (arr a, arr a)
insertAtThenSplitAt src !insIx x !splIx
  | insIx < splIx = runST $ do -- inserted element ends up in dstL
      dstL <- replicateMutable splIx x
      copy dstL 0 src 0 insIx
      copy dstL (insIx + 1) src insIx (splIx - insIx - 1)
      left <- unsafeFreeze dstL
      let right = clone src (splIx - 1) (size src - splIx + 1)
      pure (left, right)
  | otherwise = runST $ do -- inserted element ends up in dstR
    let left = clone src 0 splIx
    dstR <- replicateMutable (size src + 1 - splIx) x
    copy dstR 0 src splIx (insIx - splIx)
    copy dstR (insIx - splIx + 1) src insIx (size src - insIx)
    right <- unsafeFreeze dstR
    pure (left, right)

-- drop one element from the given index into the array and insert the two noew elements in its place
replace1To2 :: (Contiguous arr, Element arr a)
  => arr a -> Int -> a -> a -> arr a
{-# inline replace1To2 #-}
replace1To2 !src !i x y = runST $ do
  -- FIXME I may be able to eliminate a memset for primarrays
  let len0 = size src
  dst <- replicateMutable (len0 + 1) x
  copy dst 0 src 0 i
  write dst (i + 1) y
  copy dst (i + 2) src (i + 1) (len0 - i - 1)
  unsafeFreeze dst
