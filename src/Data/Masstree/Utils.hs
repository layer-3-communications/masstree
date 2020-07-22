module Data.Masstree.Utils where

-- FIXME merge these utilities upstream where it makes sense
-- then use anmed imports
import Data.Primitive.Contiguous

import Control.Monad.ST (runST)

checkedIndex :: (Contiguous arr, Element arr a) => arr a -> Int -> Maybe a
checkedIndex xs i
  | i < size xs = Just $ index xs i
  | otherwise = Nothing

findIndex :: (Contiguous arr, Element arr a) => (a -> Bool) -> arr a -> Maybe Int
findIndex p xs = loop 0
  where
  loop i
    | i < size xs = if p (index xs i) then Just i else loop (i + 1)
    | otherwise = Nothing

-- create a copy of the given array except the given index is replaced with the given value
replaceAt :: (Contiguous arr, Element arr a) => arr a -> Int -> a -> arr a
replaceAt src i x = create $ do
  dst <- thaw src 0 (size src)
  write dst i x
  pure dst

-- insert element so that it becomes the new element at the given index
-- the preceding elements remain unchanged, and the successding elemetn indexes are shifted over
insertAt :: (Contiguous arr, Element arr a) => arr a -> Int -> a -> arr a
insertAt src i x = create $ do
  let len0 = size src
  dst <- replicateMutable (len0 + 1) x
  copy dst 0 src 0 i
  copy dst (i + 1) src i (len0 - i)
  pure dst

-- split the given array at the given index (so that the length of the first is equal to the given index)
splitAt :: (Contiguous arr, Element arr a) => arr a -> Int -> (arr a, arr a)
splitAt src lenL =
  let lenR = size src - lenL
   in (clone src 0 lenL, clone src lenL lenR)
