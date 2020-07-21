{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Masstree where

import Prelude hiding (lookup)

import Control.Monad.ST (runST)
import Data.Word (Word8,Word64)

import Data.Masstree.ArrayList (ArrayList)
import Data.Primitive.SmallArray (SmallArray)

import qualified Data.Masstree.ArrayList as AL
import qualified Data.Primitive.SmallArray as SA


fanout :: Int
fanout = 8

data BTreeU64 v
  = Node
    { keys :: ArrayList Word64
      -- ^ keys delimiting the min/max entries in the children
      -- INVARIANT: length equal to children length - 1
      -- there are some "fun" design choices here: should I add two more for min/max bound of tree as a whole to speed up misses?
    , children :: SmallArray (BTreeU64 v)
      -- INVARIANT: length less than or equal to fanout
      -- INVARIANT length at least one, but also at least half the fanout if not the root node
    }
  | Leaf
    { keys :: ArrayList Word64
    , keyLens :: ArrayList Word8
    -- INVARIANT: same length as keys
    , values :: SmallArray v
    -- INVARIANT: keys and values are the same length and non-empty
    }


-- l <= 8; if l < 8, then pad input bytes with nulls on the left to obtain a Word64
lookup :: BTreeU64 v -> Word64 -> Word8 -> Maybe v
lookup Leaf{keys,keyLens,values} k l = go 0
  where
  go i
    | i < AL.length keys =
      if AL.unsafeIndex keys i == k
         && AL.unsafeIndex keyLens i == l
      then Just $ SA.indexSmallArray values i
      else go (i + 1)
    | otherwise = Nothing
lookup Node{keys,children} k l = go 0
  where
  go i
    | i < ksLen
    , AL.unsafeIndex keys i <= k
      = go (i + 1)
    | otherwise = lookup (SA.indexSmallArray children i) k l
  ksLen = AL.length keys

minKey :: BTreeU64 v -> Maybe Word64
minKey Leaf{keys} = AL.index keys 0
minKey Node{keys} = AL.index keys 0

unsafeMinKey :: BTreeU64 v -> Word64
unsafeMinKey Leaf{keys} = AL.unsafeIndex keys 0
unsafeMinKey Node{keys} = AL.unsafeIndex keys 0

insert :: forall v. BTreeU64 v -> Word64 -> Word8 -> v -> BTreeU64 v
insert root k l v = case go root of
  Left (left, right) -> Node
    { keys = AL.singleton $ unsafeMinKey right
    -- unsafeMinKey is ok because an empty tree will never split a node on insert, and therefore never make it to this branch
    , children = SA.smallArrayFromList [left, right] -- TODO is there a way to implement doubleton for small arrays
    }
  Right root' -> root'
  where
  go :: BTreeU64 v -> Either (BTreeU64 v, BTreeU64 v) (BTreeU64 v)
  go Leaf{keys,keyLens,values} = runST $ do
    let len0 = AL.length keys
    -- figure out whether to replace/insert and where
    -- Left is replace, Right is insert
    let at = case AL.findIndex keys k of
          Just i ->
            -- ensure that the key length matches as well
            let loop j
                  | j < len0
                  , AL.unsafeIndex keys j == k
                  = case compare (AL.unsafeIndex keyLens j) l of
                      LT -> loop (j + 1)
                      EQ -> Left j
                      GT -> Right j
                  | otherwise = Right j
             in loop i
          Nothing -> Right (len0 + 1)
    case at of
      -- replace
      Left i -> do
        dst <- SA.thawSmallArray values 0 len0
        SA.writeSmallArray dst i v
        values' <- SA.unsafeFreezeSmallArray dst
        pure $ Right Leaf
          { keys
          , keyLens
          , values = values'
          }
      -- insert
      -- TODO for now I'm just inserting first and splitting later
      -- I could avoid memory copying if figured out destinations ahead-of-time
      Right i -> do
        dst <- SA.newSmallArray (len0 + 1) (errThunk "Data.Masstree.insert.go(Leaf, insert)")
        SA.copySmallArray dst 0 values 0 i
        SA.writeSmallArray dst i v
        SA.copySmallArray dst (i + 1) values i (len0 - i)
        let keys' = AL.insert keys i k
        let keyLens' = AL.insert keyLens i l
        values' <- SA.unsafeFreezeSmallArray dst
        if SA.sizeofSmallArray values' <= fanout
          then pure $ Right Leaf
            { keys = keys'
            , keyLens = keyLens'
            , values = values'
            }
          else do
            let at = (len0 `div` 2) + 1
                len = len0 + 1
            let (keysL, keysR) = AL.split keys' at
            let (keyLensL, keyLensR) = AL.split keyLens' at
            dstL <- SA.newSmallArray at (errThunk "Data.Masstree.insert.go(Leaf, insert, split)")
            dstR <- SA.newSmallArray (len - at) (errThunk "Data.Masstree.insert.go(Leaf, insert, split)")
            SA.copySmallArray dstL 0 values' 0 at
            SA.copySmallArray dstR 0 values' at (len - at)
            valuesL <- SA.unsafeFreezeSmallArray dstL
            valuesR <- SA.unsafeFreezeSmallArray dstR
            let left = Leaf{keys = keysL, keyLens = keyLensL, values = valuesL}
                right = Leaf{keys = keysR, keyLens = keyLensR, values = valuesR}
            pure $ Left (left, right)
    -- | len <- AL.length keys
    -- , len < fanout = runST $ do
    --   dst <- SA.newSmallArray (len + 1) (errThunk "Data.Masstree.insert.go(Leaf < fanout)")
    --   let loop i
    --         | i < len = case compare (AL.unsafeIndex keys i, AL.unsafeIndex keyLens i) (k, l) of
    --           LT -> do
    --             SA.writeSmallArray dst i (SA.indexSmallArray values i)
    --             loop (i + 1)
    --           EQ -> do
    --             SA.writeSmallArray dst i (SA.indexSmallArray values i)
    --             SA.copySmallArray dst (i + 1) values i (len - i)
    --             pure Nothing
    --           GT -> undefined
    --         | otherwise = do
    --             SA.writeSmallArray dst i v
    --             pure $ Just i
    --   i <- loop 0
    --   values' <- SA.unsafeFreezeSmallArray dst
    --   pure $ Right Leaf
    --     { keys = AL.insert keys i k
    --     , keyLens = AL.insert keyLens i l
    --     , values = values'
    --     }
    -- | otherwise = undefined -- TODO split
  -- go Node{keys,children} -- TODO

errThunk :: String -> a
errThunk here = errorWithoutStackTrace $ "uninitialized value created in " ++ here
