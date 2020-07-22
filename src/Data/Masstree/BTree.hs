{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Masstree.BTree
  ( BTree(..)
  , empty
  , lookup
  , insert
  , toList
  , fromList
  ) where

import Prelude hiding (lookup)

import Data.Functor ((<&>))
import Data.Functor.Identity (runIdentity)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Word (Word64)


import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.Utils as Arr
import qualified GHC.Exts as Exts
import qualified Data.Foldable as Foldable


fanout :: Int
fanout = 8

-- | A BTree.
--
-- The data constructors are only exported for testing. Do not use these.
data BTree v
  = Branch
    { keys :: !(PrimArray Word64)
      -- ^ keys delimiting the min/max entries in the children
      -- INVARIANT: length equal to children length - 1
      -- there are some "fun" design choices here: should I add two more for min/max bound of tree as a whole to speed up misses?
    , children :: !(SmallArray (BTree v))
      -- INVARIANT: length less than or equal to fanout
      -- INVARIANT length at least one, but also at least half the fanout if not the root node
    }
  | Leaf
    { keys :: !(PrimArray Word64)
    , values :: !(SmallArray v)
    -- INVARIANT: keys and values are the same length and non-empty
    }

empty :: BTree v
empty = Leaf{keys=mempty,values=mempty}

-- l <= 8; if l < 8, then pad input bytes with nulls on the left to obtain a Word64
lookup :: BTree v -> Word64 -> Maybe v
lookup Leaf{keys,values} k = case findInsRep keys k of
  Left _ -> Nothing
  Right i -> Just $ Arr.index values i
lookup Branch{keys,children} k = lookup (Arr.index children $ findChild keys k) k


insert :: BTree v -> Word64 -> v -> BTree v
insert t k v = runIdentity $ upsertF (pure . const v) t k

data Result v
  = Split !(BTree v) {-# UNPACK #-} !Word64 !(BTree v)
  | Ok !(BTree v)

upsertF :: forall f v. (Functor f) => (Maybe v -> f v) -> BTree v -> Word64 -> f (BTree v)
upsertF f root k = go root <&> \case
  Ok root' -> root'
  Split left keyM right -> Branch
    -- unsafeMinKey is ok because an empty tree will never split a node on insert, and therefore never make it to this branch
    { keys = Arr.singleton keyM
    , children = Arr.doubleton left right
    }
  where
  go :: BTree v -> f (Result v)
  go Leaf{keys,values} = case findInsRep keys k of
    -- replace
    Right i -> Arr.modifyAtF (f . Just) values i <&> \values' ->
      Ok Leaf {keys, values = values' }
    -- insert
    -- TODO for now I'm just inserting first and splitting later
    -- I could avoid some memory copying if I figured out destinations ahead-of-time
    Left i -> f Nothing <&> \v ->
      let keys' = Arr.insertAt keys i k
          values' = Arr.insertAt values i v
       in if Arr.size values' <= fanout
          then Ok
            Leaf {keys = keys', values = values'}
          else
            let at = (Arr.size keys `div` 2) + 1
                (keysL, keysR) = Arr.splitAt keys' at
                keyM = Arr.index keysR 0
                (valuesL, valuesR) = Arr.splitAt values' at
                left = Leaf{keys = keysL, values = valuesL}
                right = Leaf{keys = keysR, values = valuesR}
             in Split left keyM right
  go Branch{keys,children} =
    let i = findChild keys k
     in go (Arr.index children i) <&> \case
        Split left keyM right ->
          -- TODO for now I'm just inserting first and splitting later
          -- I could avoid some memory copying if I figured out destinations ahead-of-time
          let keys' = Arr.insertAt keys i keyM
              -- TODO replace after insertAt? what hilarious amounts of copying!
              children' = Arr.replaceAt (Arr.insertAt children i left) (i + 1) right
           in if Arr.size children' <= fanout
              then Ok
                Branch {keys = keys', children = children'}
              else
                let at = (Arr.size children `div` 2) + 1
                    keysL' = Arr.clone keys' 0 (at - 1)
                    keyM' = Arr.index keys' (at - 1)
                    keysR' = Arr.clone keys' at (Arr.size keys' - at)
                    (childrenL, childrenR) = Arr.splitAt children' at
                    left' = Branch {keys = keysL', children = childrenL}
                    right' = Branch {keys = keysR', children = childrenR}
                 in Split left' keyM' right'
        Ok child' -> Ok Branch
          { keys -- don't have to update the keys, since the new children
                 -- won't have a key smaller than it already had
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

-- find the index of a child to recurse into given a key to search for
findChild :: PrimArray Word64 -> Word64 -> Int
findChild keys k = go 0
  where
  go i
    | i >= Arr.size keys = Arr.size keys
    | k >= Arr.index keys i = go (i + 1)
    | otherwise = i

-- | Lazy right foldr over all key-value pairs in a BTree.
foldrWithKey :: forall v b. (Word64 -> v -> b -> b) -> b -> BTree v -> b
foldrWithKey f b0 tree0 = go tree0 b0
  where
  go :: BTree v -> b -> b
  go tree b = case tree of
    Leaf{keys,values} -> Arr.foldrZipWith f b keys values
    Branch{children} -> Arr.foldr go b children

-- | Convert a BTree to a list of key-value pairs.
toList :: BTree v -> [(Word64,v)]
toList = foldrWithKey (\k v xs -> (k,v) : xs) []

-- | Build a BTree from a list of key-value pairs.
fromList :: [(Word64,v)] -> BTree v
fromList = Foldable.foldl' (\acc (k,v) -> insert acc k v) empty

-- | Low performance @Eq@ instance. Only really needed for tests.
instance Eq v => Eq (BTree v) where
  a == b = toList a == toList b

-- | Low performance @Semigroup@ instance. Worth improving if merging
-- BTrees is a common operation for anyone.
--
-- Also, currently somewhat incorrect. This discards earlier elements
-- in favor of later ones. Rewrite this to use a Semigroup instance on
-- the values.
instance Semigroup (BTree v) where
  a0 <> b = foldrWithKey (\k v acc -> insert acc k v) a0 b

instance Monoid (BTree v) where
  mempty = empty

instance Exts.IsList (BTree v) where
  type Item (BTree v) = (Word64,v)
  toList = toList
  fromList = fromList

-- | Shows a list of key-value pairs present in the BTree.
instance Show v => Show (BTree v) where
  showsPrec d b = showsPrec d (toList b)
