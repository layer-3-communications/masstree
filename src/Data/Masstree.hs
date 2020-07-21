{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Masstree where

import Prelude hiding (lookup)

import Data.Maybe (fromMaybe)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Word (Word8,Word64)


import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.Utils as Arr


fanout :: Int
fanout = 8

data BTreeU64 v
  = Branch
    { keys :: PrimArray Word64
      -- ^ keys delimiting the min/max entries in the children
      -- INVARIANT: length equal to children length - 1
      -- there are some "fun" design choices here: should I add two more for min/max bound of tree as a whole to speed up misses?
    , children :: SmallArray (BTreeU64 v)
      -- INVARIANT: length less than or equal to fanout
      -- INVARIANT length at least one, but also at least half the fanout if not the root node
    }
  | Leaf
    { keys :: PrimArray Word64
    , keyLens :: PrimArray Word8
    -- INVARIANT: same length as keys
    , values :: SmallArray v
    -- INVARIANT: keys and values are the same length and non-empty
    }

empty :: BTreeU64 a
empty = Leaf {keys = Arr.empty, keyLens = Arr.empty, values = Arr.empty}

singleton :: Word64 -> Word8 -> a -> BTreeU64 a
singleton k l v = Leaf
  { keys = Arr.singleton k
  , keyLens = Arr.singleton l
  , values = Arr.singleton v
  }

-- l <= 8; if l < 8, then pad input bytes with nulls on the left to obtain a Word64
lookup :: BTreeU64 v -> Word64 -> Word8 -> Maybe v
lookup Leaf{keys,keyLens,values} k l =
  go $ fromMaybe (Arr.size keys) (Arr.findIndex (==k) keys)
  where
  go i
    | i < Arr.size keys
    , Arr.index keys i == k
    = case compare (Arr.index keyLens i) l of
        LT -> go (i + 1)
        EQ -> Just $ Arr.index values i
        GT -> Nothing
    | otherwise = Nothing
lookup Branch{keys,children} k l = case Arr.findIndex (< k) keys of
  Just i -> lookup (Arr.index children i) k l
  Nothing -> lookup (Arr.index children (Arr.size keys)) k l -- look in the last child

insert :: forall v. BTreeU64 v -> Word64 -> Word8 -> v -> BTreeU64 v
insert root k l v = case go root of
  Right root' -> root'
  Left (left, keyM, right) -> Branch
    -- unsafeMinKey is ok because an empty tree will never split a node on insert, and therefore never make it to this branch
    { keys = Arr.singleton keyM
    , children = Arr.doubleton left right
    }
  where
  go :: BTreeU64 v -> Either (BTreeU64 v, Word64, BTreeU64 v) (BTreeU64 v)
  go Leaf{keys,keyLens,values} = case findInsRep keys k keyLens l of
    -- replace
    Left i -> Right
      Leaf {keys, keyLens, values = Arr.replaceAt values i v}
    -- insert
    -- TODO for now I'm just inserting first and splitting later
    -- I could avoid some memory copying if I figured out destinations ahead-of-time
    Right i ->
      let keys' = Arr.insertAt keys i k
          keyLens' = Arr.insertAt keyLens i l
          values' = Arr.insertAt values i v
       in if Arr.size values' <= fanout
          then Right
            Leaf {keys = keys', keyLens = keyLens', values = values'}
          else
            let at = (Arr.size keys `div` 2) + 1
                (keysL, keysR) = Arr.splitAt keys' at
                keyM = Arr.index keysR 0
                (keyLensL, keyLensR) = Arr.splitAt keyLens' at
                (valuesL, valuesR) = Arr.splitAt values' at
                left = Leaf{keys = keysL, keyLens = keyLensL, values = valuesL}
                right = Leaf{keys = keysR, keyLens = keyLensR, values = valuesR}
             in Left (left, keyM, right)
  go Branch{keys,children} =
    let i = fromMaybe (Arr.size keys) (Arr.findIndex (<= k) keys)
     in case go (Arr.index children i) of
        Left (left, keyM, right) ->
          -- TODO for now I'm just inserting first and splitting later
          -- I could avoid some memory copying if I figured out destinations ahead-of-time
          let keys' = Arr.insertAt keys i keyM
              -- TODO replace after insertAt? what hilarious amounts of copying!
              children' = Arr.replaceAt (Arr.insertAt children i left) (i + 1) right
           in if Arr.size children' <= fanout
              then Right
                Branch {keys = keys', children = children'}
              else
                let at = (Arr.size children `div` 2) + 1
                    keysL' = Arr.clone keys 0 (at - 1)
                    keyM' = Arr.index keys (at - 1)
                    keysR' = Arr.clone keys at (Arr.size keys - at)
                    (childrenL, childrenR) = Arr.splitAt children at
                    left' = Branch {keys = keysL', children = childrenL}
                    right' = Branch {keys = keysR', children = childrenR}
                 in Left (left', keyM', right')
        Right child' -> Right Branch
          { keys -- don't have to update the keys, since  the new children won't have a key smaller than it already had
          , children = Arr.replaceAt children i child'
          }

-- WARNING xs, ys must have same size
-- left for insert, right for replace
findInsRep :: PrimArray Word64 -> Word64 -> PrimArray Word8 -> Word8 -> Either Int Int
findInsRep keys k lengths l =
  let i0 = fromMaybe (Arr.size keys) (Arr.findIndex (k <) keys)
   in loop i0
  where
  loop i
    | i < Arr.size keys
    , Arr.index keys i == k
    = case compare (Arr.index lengths i) l of
        LT -> loop (i + 1)
        EQ -> Left i
        GT -> Right i
    | otherwise = Right i
