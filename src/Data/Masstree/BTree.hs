{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedSums #-}

-- | This module defines a B+-tree, which is a balanced /n/-ary search tree for
-- a fixed /n/ with values stored at the leaves. It is specialized to keys of
-- type 'Word64', and thereby could play a role similar to "Data.IntMap".
-- However, it is meant specifically for the implementation of masstrees in
-- "Data.Masstree".
--
-- TODO: deletions based on <http://sidsen.azurewebsites.net/papers/relaxed-b-tree-tods.pdf>
--
-- TODO: prefix compression
module Data.Masstree.BTree
  ( BTree(..)
  , empty
  , singleton
  , null
  , lookup
  , insert
  , insertWith
  , upsert
  , upsertF
  , toList
  , fromList
  , foldrWithKey
  , foldlWithKeyM'
  , size
  , toArrays
  , fromSortedArrays
    -- * Unstable
  , height
  ) where

import Prelude hiding (lookup,null)

import Control.Monad.ST.Run (runSmallArrayST,runPrimArrayST)
import Data.Functor ((<&>))
import Data.Functor.Identity (runIdentity)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray,SmallMutableArray)
import Data.Word (Word64)
import Control.Monad.ST (ST,runST)
import GHC.Exts (Int(I#),Int#)

import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.Utils as Arr
import qualified GHC.Exts as Exts
import qualified Data.Foldable as Foldable

fanout :: Int
fanout = 8

-- | A B+ tree with a fanout of 8 for use in memory.
--
-- The data constructors are only exported for testing. Do not use these.
data BTree v
  = Branch
    { keys :: !(PrimArray Word64)
      -- ^ Keys delimiting the min/max entries in the children.
      -- The @i@th key is the greatest lower bound on the @i+1@st child's keyset.
      --
      -- INVARIANT: @length keys == length children - 1@
      --
      -- TODO there are some "fun" design choices here: should I add two more for min/max bound of tree as a whole to speed up misses?
    , children :: !(SmallArray (BTree v))
      -- ^ INVARIANT: @1 <= length children <= fanout@
    }
  | Leaf
    { keys :: !(PrimArray Word64)
      -- ^ Individual keys for each value stored at this node.
    , values :: !(SmallArray v)
      -- ^ The @i@th value here corresponds to the key stored at index @i@ in @keys@.
      --
      -- INVARIANT: @keys@ and @values@ are the same length and non-empty
    }
  deriving stock (Functor,Foldable,Traversable)

-- | /O(1)/ Is the map empty?
null :: BTree v -> Bool
null Branch{} = False
null Leaf{values} = PM.sizeofSmallArray values == 0

-- | /O(1)/.
-- The empty map.
empty :: BTree v
empty = Leaf{keys=mempty,values=mempty}

-- | /O(1)/.
-- A map with a single element.
singleton :: Word64 -> v -> BTree v
singleton k v = Leaf{keys = Arr.singleton k, values=Arr.singleton v}

-- FIXME move this documentation: l <= 8; if l < 8, then pad input bytes with nulls on the left to obtain a Word64
-- | /O(log n)/.
-- Lookup the value at a key in the map.
--
-- The function will return the corresponding value as (Just value), or Nothing if the key isn't in the map.
lookup :: Word64 -> BTree v -> Maybe v
lookup !k Leaf{keys,values} = case findInsRep keys k of
  RightInt# i -> Just $ Arr.index values (I# i)
  _ -> Nothing
lookup !k Branch{keys,children} = lookup k (Arr.index children $ findChild keys k)

-- | /O(log n)/.
-- Insert a new key and value in the map. If the key is already present in the
-- map, the associated value is replaced with the supplied value. 'insert' is
-- equivalent to @'insertWith' 'const'@.
insert :: Word64 -> v -> BTree v -> BTree v
insert = insertWith const

-- | /O(log n)/.
-- Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@ will insert the pair @(key, value)@ into @mp@
-- if @key@ does not exist in the map.
-- If the key does exist, the function will insert the pair]
-- @(key, f new_value old_value)@.
insertWith :: (v -> v -> v) -> Word64 -> v -> BTree v -> BTree v
insertWith f k v = upsert (maybe v (flip f v)) k

-- | /O(log n)/.
-- 'upsert' may be used to update or insert a value in a 'BTree'.
-- In short: @'lookup' k ('upsert' f k t0) === f ('lookup' k t0)@.
upsert :: (Maybe v -> v) -> Word64 -> BTree v -> BTree v
upsert f k = runIdentity . upsertF (pure . f) k

data Result v
  = Split !(BTree v) {-# UNPACK #-} !Word64 !(BTree v)
  | Ok !(BTree v)

-- | /O(log n)/.
-- Like 'upsert' 'upsertF' can insert or update a value in a 'BTree', but the
-- updating function operates in a functorial context.
--
-- In short: @'lookup' k '<$>' 'upsertF' f k t0 === f ('lookup' k t0)@.
--
-- Note: In theory, this should only require a 'Functor' constraint, not 'Monad'.
-- Unfortunately, it is difficult to get good guarantees about thunk leaks without
-- using 'Monad'.
upsertF :: forall f v. (Monad f) => (Maybe v -> f v) -> Word64 -> BTree v -> f (BTree v)
{-# INLINABLE upsertF #-}
{-# SPECIALIZE upsertF :: (Maybe v -> ST s v) -> Word64 -> BTree v -> ST s (BTree v) #-}
upsertF f !k root = go root <&> \case
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
    RightInt# i -> Arr.modifyAtF' (f . Just) values (I# i) <&> \values' ->
      Ok Leaf {keys, values = values' }
    -- insert
    -- TODO? for now I'm just inserting first and splitting later
    -- theoretically, insertAtThenSplitAt should be faster, but it seems it isn't...?
    LeftInt# i -> f Nothing <&> \v ->
      let !keys' = Arr.primInsertAt keys (I# i) k
          !values' = Arr.smallInsertAt values (I# i) v
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
          let !keys' = Arr.primInsertAt keys i keyM
              !children' = Arr.replace1To2 children i left right
           in if Arr.size children' <= fanout
              then Ok
                Branch {keys = keys', children = children'}
              else
                let at = (Arr.size children `div` 2) + 1
                    keysL' = Arr.clone (Arr.slice keys' 0 (at - 1))
                    keyM' = Arr.index keys' (at - 1)
                    keysR' = Arr.clone (Arr.slice keys' at (Arr.size keys' - at))
                    (childrenL, childrenR) = Arr.splitAt children' at
                    left' = Branch {keys = keysL', children = childrenL}
                    right' = Branch {keys = keysR', children = childrenR}
                 in Split left' keyM' right'
        Ok child' -> Ok Branch
          { keys -- don't have to update the keys, since the new children
                 -- won't have a key smaller than it already had
          , children = Arr.replaceAt children i child'
          }

type EitherIntInt# = (# Int# | Int# #)

pattern LeftInt# :: Int# -> EitherIntInt#
pattern LeftInt# x = (# x | #)

pattern RightInt# :: Int# -> EitherIntInt#
pattern RightInt# x = (# | x #)

{-# COMPLETE LeftInt#, RightInt# #-}

-- WARNING xs, ys must have same size
-- given a (ascending) sorted array, find the index of the given key, or else find the index where they key should be inserted
-- right for found key, left for insert point
findInsRep :: PrimArray Word64 -> Word64 -> EitherIntInt#
findInsRep !keys !k = case Arr.findIndex (k <=) keys of
  Just i@(I# i#)
    | Arr.index keys i == k -> RightInt# i#
    | otherwise -> LeftInt# i#
  Nothing -> case Arr.size keys of { I# sz# -> LeftInt# sz# }

-- find the index of a child to recurse into given a key to search for
findChild :: PrimArray Word64 -> Word64 -> Int
findChild !keys !k = go 0
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

-- | Strict monadic left fold over all key-value pairs in a BTree.
foldlWithKeyM' :: forall m v b. Monad m => (b -> Word64 -> v -> m b) -> b -> BTree v -> m b
{-# inline foldlWithKeyM' #-}
foldlWithKeyM' f b0 tree0 = go b0 tree0
  where
  go :: b -> BTree v -> m b
  go b tree = case tree of
    Leaf{keys,values} -> Arr.foldlZipWithM' f b keys values
    Branch{children} -> Arr.foldlM' go b children

-- | Convert a BTree to a list of key-value pairs.
toList :: BTree v -> [(Word64,v)]
toList = foldrWithKey (\k v xs -> (k,v) : xs) []

-- | Build a BTree from a list of key-value pairs.
--
-- WARNING: this creates the worst-possible BTree structure when fed a sorted]
-- list.
fromList :: [(Word64,v)] -> BTree v
fromList = Foldable.foldl' (\acc (k,v) -> insert k v acc) empty

-- | Convert a BTree to an array of all of the keys and an array
-- of all of the values. The array of keys is in ascending order.
--
-- Postcondition: the lengths of the returned arrays are the same as
-- one another.
toArrays :: forall v. BTree v -> (PrimArray Word64, SmallArray v)
{-# noinline toArrays #-}
toArrays b0 = runST action where
  action :: forall s. ST s (PrimArray Word64, SmallArray v)
  action = do
    let sz = size b0
    keysDst <- PM.newPrimArray sz
    valsDst <- PM.newSmallArray sz errorThunk
    let go :: Int -> BTree v -> ST s Int
        go !ixDst x = case x of
          Branch{children} -> Foldable.foldlM go ixDst children
          Leaf{keys,values} -> do
            let n = PM.sizeofSmallArray values
            PM.copySmallArray valsDst ixDst values 0 n
            PM.copyPrimArray keysDst ixDst keys 0 n
            pure (ixDst + n)
    !_ <- go 0 b0
    keys' <- PM.unsafeFreezePrimArray keysDst
    vals' <- PM.unsafeFreezeSmallArray valsDst
    pure (keys',vals')


-- | Create a BTree from an array of keys and an array of values.
--
-- Precondition: array of keys is sorted in ascending order
-- Precondition: array of keys and array of values are same length
fromSortedArrays :: forall v. PrimArray Word64 -> SmallArray v -> BTree v
{-# noinline fromSortedArrays #-}
fromSortedArrays !ks0 !vs0
  | PM.sizeofPrimArray ks0 /= len =
      errorWithoutStackTrace "Data.Masstree.BTree.fromSortedArrays: length mismatch"
  | len == 0 = empty
  | isAscending (PM.indexPrimArray ks0 0) 1 =
      let dividedLen = div len fanout
       in case dividedLen of
            0 -> Leaf
              { keys = PM.clonePrimArray ks0 0 len
              , values = PM.cloneSmallArray vs0 0 len
              }
            _ ->
              let truncLen = fanout * dividedLen
                  nodesSize = 1 + dividedLen
                  leaves = runSmallArrayST $ do
                    -- nodesSize must be at least two
                    dst <- PM.newSmallArray nodesSize errorThunk
                    let finalTwoLen = 8 + len - truncLen
                    let ultimateLen = div finalTwoLen 2
                    let ultimateIx = len - ultimateLen
                    let penultimateLen = finalTwoLen - ultimateLen
                    let penultimateIx = len - finalTwoLen
                    -- starts by cleaning up the ragged part at the end
                    PM.writeSmallArray dst (nodesSize - 1) $! Leaf
                      { keys = PM.clonePrimArray ks0 ultimateIx ultimateLen
                      , values = PM.cloneSmallArray vs0 ultimateIx ultimateLen
                      }
                    PM.writeSmallArray dst (nodesSize - 2) $! Leaf
                      { keys = PM.clonePrimArray ks0 penultimateIx penultimateLen
                      , values = PM.cloneSmallArray vs0 penultimateIx penultimateLen
                      }
                    buildFullLeaves 0 0 (nodesSize - 2) dst
               in chunkNodes nodesSize leaves
  | otherwise =
      errorWithoutStackTrace "Data.Masstree.BTree.fromSortedArrays: nonascending keys"
  where
  !len = PM.sizeofSmallArray vs0
  isAscending !prev !ix = if ix < len
    then
      let next = PM.indexPrimArray ks0 ix 
       in if prev < next
            then isAscending next (ix + 1)
            else False
    else True
  -- Note: buildFullLeaves only creates full leaves. The final two
  -- underfull leaves are expected to already be filled in before this
  -- function is called.
  buildFullLeaves :: forall s. Int -> Int -> Int -> SmallMutableArray s (BTree v) -> ST s (SmallArray (BTree v))
  buildFullLeaves !ix !dstIx !remainingNodes !dst = case remainingNodes of
    0 -> PM.unsafeFreezeSmallArray dst
    _ -> do
      let keys = PM.clonePrimArray ks0 ix fanout
      let values = PM.cloneSmallArray vs0 ix fanout
      let !node = Leaf{keys,values}
      PM.writeSmallArray dst dstIx node
      buildFullLeaves (ix + fanout) (dstIx + 1) (remainingNodes - 1) dst

-- Internal function.
-- Precondition: argument array has size >= 2
-- Precondition: all nodes in argument array are non-empty
-- Precondition: len argument agrees with size of small array argument
chunkNodes :: forall v. Int -> SmallArray (BTree v) -> BTree v
chunkNodes !len !nodes =
  let dividedLen = div len fanout
   in case dividedLen of
        0 -> Branch
          { keys = sliceNodeMinimumKeys len nodes
          , children = PM.cloneSmallArray nodes 0 len
          }
        _ ->
          let truncLen = fanout * dividedLen
              nodesSize = 1 + dividedLen
              leaves = runSmallArrayST $ do
                -- nodesSize must be at least two
                dst <- PM.newSmallArray nodesSize errorThunk
                let finalTwoLen = 8 + len - truncLen
                let ultimateLen = div finalTwoLen 2
                let ultimateIx = len - ultimateLen
                let penultimateLen = finalTwoLen - ultimateLen
                let penultimateIx = len - finalTwoLen
                -- starts by cleaning up the ragged part at the end
                let ultimateValues = PM.cloneSmallArray nodes ultimateIx ultimateLen
                PM.writeSmallArray dst (nodesSize - 1) $! Branch
                  { keys = sliceNodeMinimumKeys ultimateLen ultimateValues
                  , children = ultimateValues
                  }
                let penultimateValues = PM.cloneSmallArray nodes penultimateIx penultimateLen
                PM.writeSmallArray dst (nodesSize - 2) $! Branch
                  { keys = sliceNodeMinimumKeys penultimateLen penultimateValues
                  , children = penultimateValues
                  }
                buildFullNodes 0 0 (nodesSize - 2) dst
           in chunkNodes nodesSize leaves
  where
  buildFullNodes :: forall s. Int -> Int -> Int -> SmallMutableArray s (BTree v) -> ST s (SmallArray (BTree v))
  buildFullNodes !ix !dstIx !remainingNodes !dst = case remainingNodes of
    0 -> PM.unsafeFreezeSmallArray dst
    _ -> do
      let children = PM.cloneSmallArray nodes ix fanout
      let !node = Branch{keys=sliceNodeMinimumKeys fanout children,children}
      PM.writeSmallArray dst dstIx node
      buildFullNodes (ix + fanout) (dstIx + 1) (remainingNodes - 1) dst

-- Precondition: argument size >= 1
-- Postcondition: size of result array is 1 less than size of argument array
sliceNodeMinimumKeys :: Int -> SmallArray (BTree v) -> PrimArray Word64
sliceNodeMinimumKeys !len !nodes = runPrimArrayST $ do
  dst <- PM.newPrimArray (len - 1)
  let go !ix !ixDst = case ixDst of
        (-1) -> PM.unsafeFreezePrimArray dst
        _ -> do
          k <- PM.indexSmallArrayM nodes ix >>= \case
            Leaf{keys} -> pure (PM.indexPrimArray keys 0)
            Branch{keys} -> pure (PM.indexPrimArray keys 0)
          PM.writePrimArray dst ixDst k
          go (ix - 1) (ixDst - 1)
  go (len - 1) (len - 2)

errorThunk :: a
{-# noinline errorThunk #-}
errorThunk = errorWithoutStackTrace "Data.Masstree.BTree: implementation mistake"

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
  a0 <> b = foldrWithKey insert a0 b

instance Monoid (BTree v) where
  mempty = empty

instance Exts.IsList (BTree v) where
  type Item (BTree v) = (Word64,v)
  toList = toList
  fromList = fromList

-- | Shows a list of key-value pairs present in the BTree.
instance Show v => Show (BTree v) where
  showsPrec d b = showsPrec d (toList b)

-- | The height of the BTree. Since the BTrees in this library are
-- of degree 8, the height provides a coarse approximation of the
-- number of elements in the BTree:
--
-- * Height 0: 0-8 elements
-- * Height 1: 9-64 elements
-- * Height 2: 65-512 elements
-- * Height 3: 513-4096 elements
-- * Height 4: 4097-32768 elements
-- * Height 5: 32769-262144 elements
--
-- WARNING: This function is not stable. Currently, the fanout is set
-- to 8, but if this ever were to change, then the height of some trees
-- would change. Nevertheless, this is a useful tool for approximating
-- cardinality without having to walk the entire data structure.
height :: BTree v -> Int
height = go 0 where
  go :: Int -> BTree v -> Int
  go !h Leaf{} = h
  go !h Branch{children} = go (h + 1) (PM.indexSmallArray children 0)

-- | /O(n)/ The number of entries in the BTree. This operation requires
-- walking this entire BTree.
size :: BTree v -> Int
size = go where
  go :: BTree v -> Int
  go Leaf{values} = PM.sizeofSmallArray values
  go Branch{children} = Foldable.foldl' (\acc b -> acc + go b) 0 children
