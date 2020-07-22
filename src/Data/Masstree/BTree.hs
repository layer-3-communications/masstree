{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Masstree.BTree where

import Prelude hiding (lookup)

import Data.Maybe (fromMaybe)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Word (Word64)


import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.Utils as Arr


fanout :: Int
fanout = 8

data BTree v
  = Branch
    { keys :: PrimArray Word64
      -- ^ keys delimiting the min/max entries in the children
      -- INVARIANT: length equal to children length - 1
      -- there are some "fun" design choices here: should I add two more for min/max bound of tree as a whole to speed up misses?
    , children :: SmallArray (BTree v)
      -- INVARIANT: length less than or equal to fanout
      -- INVARIANT length at least one, but also at least half the fanout if not the root node
    }
  | Leaf
    { keys :: PrimArray Word64
    , values :: SmallArray v
    -- INVARIANT: keys and values are the same length and non-empty
    }


-- l <= 8; if l < 8, then pad input bytes with nulls on the left to obtain a Word64
lookup :: BTree v -> Word64 -> Maybe v
lookup Leaf{keys,values} k = case findInsRep keys k of
  Left _ -> Nothing
  Right i -> Just $ Arr.index values i
lookup Branch{keys,children} k = case Arr.findIndex (< k) keys of
  Just i -> lookup (Arr.index children i) k
  Nothing -> lookup (Arr.index children (Arr.size keys)) k -- look in the last child

insert :: forall v. BTree v -> Word64 -> v -> BTree v
insert root k v = case go root of
  Right root' -> root'
  Left (left, keyM, right) -> Branch
    -- unsafeMinKey is ok because an empty tree will never split a node on insert, and therefore never make it to this branch
    { keys = Arr.singleton keyM
    , children = Arr.doubleton left right
    }
  where
  go :: BTree v -> Either (BTree v, Word64, BTree v) (BTree v)
  go Leaf{keys,values} = case findInsRep keys k of
    -- replace
    Right i -> Right
      Leaf {keys, values = Arr.replaceAt values i v}
    -- insert
    -- TODO for now I'm just inserting first and splitting later
    -- I could avoid some memory copying if I figured out destinations ahead-of-time
    Left i ->
      let keys' = Arr.insertAt keys i k
          values' = Arr.insertAt values i v
       in if Arr.size values' <= fanout
          then Right
            Leaf {keys = keys', values = values'}
          else
            let at = (Arr.size keys `div` 2) + 1
                (keysL, keysR) = Arr.splitAt keys' at
                keyM = Arr.index keysR 0
                (valuesL, valuesR) = Arr.splitAt values' at
                left = Leaf{keys = keysL, values = valuesL}
                right = Leaf{keys = keysR, values = valuesR}
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
-- given a (ascending) sorted array, find the index of the given key, or else find the index where they key should be inserted
-- right for found key, left for insert point
findInsRep :: PrimArray Word64 -> Word64 -> Either Int Int
findInsRep keys k = case Arr.findIndex (k <=) keys of
  Just i
    | Arr.index keys i == k -> Right i
    | otherwise -> Left i
  Nothing -> Left $ Arr.size keys
