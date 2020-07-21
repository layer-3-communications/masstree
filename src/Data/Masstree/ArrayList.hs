module Data.Masstree.ArrayList where

import Control.Monad.ST (runST)
import Data.Primitive (Prim, PrimArray)

import qualified Data.Primitive as PM

data ArrayList a = ArrayList { unArrayList :: {-# UNPACK #-} !(PrimArray a) }
  deriving (Show)

empty :: Prim a => ArrayList a
empty = runST $ do
  dst <- PM.newPrimArray 0
  arr <- PM.unsafeFreezePrimArray dst
  pure $ ArrayList arr

singleton :: Prim a => a -> ArrayList a
singleton x = runST $ do
  dst <- PM.newPrimArray 1
  PM.writePrimArray dst 0 x
  arr <- PM.unsafeFreezePrimArray dst
  pure $ ArrayList arr

doubleton :: Prim a => a -> a -> ArrayList a
doubleton x y = runST $ do
  dst <- PM.newPrimArray 2
  PM.writePrimArray dst 0 x
  PM.writePrimArray dst 1 y
  arr <- PM.unsafeFreezePrimArray dst
  pure $ ArrayList arr

insert :: Prim a => ArrayList a -> Int -> a -> ArrayList a
insert (ArrayList src) i x = runST $ do
  let len0 = PM.sizeofPrimArray src
  dst <- PM.newPrimArray (len0 + 1)
  PM.copyPrimArray dst 0 src 0 i
  PM.writePrimArray dst i x
  PM.copyPrimArray dst (i + 1) src i (len0 - i)
  arr <- PM.unsafeFreezePrimArray dst
  pure $ ArrayList arr

split :: Prim a => ArrayList a -> Int -> (ArrayList a, ArrayList a)
split (ArrayList src) at = runST $ do
  let len0 = PM.sizeofPrimArray src
  dstL <- PM.newPrimArray at
  dstR <- PM.newPrimArray (len0 - at)
  PM.copyPrimArray dstL 0 src 0 at
  PM.copyPrimArray dstR 0 src at (len0 - at)
  arrL <- PM.unsafeFreezePrimArray dstL
  arrR <- PM.unsafeFreezePrimArray dstR
  pure (ArrayList arrL, ArrayList arrR)

-- split the source array in half, then insert the value in one side or the other
splitInsert :: Prim a => ArrayList a -> Int -> a -> (ArrayList a, ArrayList a)
splitInsert (ArrayList src) i x = runST $ do
  let len0 = PM.sizeofPrimArray src
      (lenL, lenR) = case (len0 + 1) `divMod` 2 of
        (0, l) -> (l, l)
        (_, l) -> (l + 1, l)
  dstL <- PM.newPrimArray lenL
  dstR <- PM.newPrimArray lenR
  if (i < lenL)
    then do
      PM.copyPrimArray dstL 0 src 0 i
      PM.writePrimArray dstL i x
      PM.copyPrimArray dstL (i + 1) src i (lenL - i - 1)
      PM.copyPrimArray dstR 0 src lenL lenR
    else do
      let i' = i - lenL
      PM.copyPrimArray dstL 0 src 0 lenL
      PM.copyPrimArray dstR 0 src lenL i'
      PM.writePrimArray dstR i' x
      PM.copyPrimArray dstR (i' + 1) src i (lenR - i' - 1)
  arrL <- PM.unsafeFreezePrimArray dstL
  arrR <- PM.unsafeFreezePrimArray dstR
  pure (ArrayList arrL, ArrayList arrR)


length :: Prim a => ArrayList a -> Int
length = PM.sizeofPrimArray . unArrayList

index :: Prim a => ArrayList a -> Int -> Maybe a
index (ArrayList xs) ix
  | ix < PM.sizeofPrimArray xs = Just $ PM.indexPrimArray xs ix
  | otherwise = Nothing

unsafeIndex :: Prim a => ArrayList a -> Int -> a
unsafeIndex (ArrayList xs) ix = PM.indexPrimArray xs ix

findIndex :: (Prim a, Eq a) => ArrayList a -> a -> Maybe Int
findIndex (ArrayList haystack) needle = go 0
  where
  go i
    | i < PM.sizeofPrimArray haystack =
      if PM.indexPrimArray haystack i == needle then Just i else go (i + 1)
    | otherwise = Nothing
