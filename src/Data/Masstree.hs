{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Masstree where

import Prelude hiding (lookup)

import Data.Bits ((.|.), unsafeShiftL)
import Data.Bytes (Bytes)
import Data.Masstree.BTree (BTree)
import Data.Maybe (fromMaybe)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Word (Word8,Word64)

import qualified Data.Bytes as Bytes
import qualified Data.Masstree.BTree as BTree
import qualified Data.Masstree.Utils as Arr
import qualified Data.Primitive.Contiguous as Arr


data Masstree v = Masstree
  { keys :: PrimArray Word64
  -- ^ keys for the values at this node; parallels `lengths` and `values`
  , lengths :: PrimArray Int
  -- ^ lengths of keys at this node (1-8); parallels `keys` and `values`
  -- the root node is also allowed to have an entry of length zero
  , values :: SmallArray v
  -- ^ values at this node; parallels `keys` and `lengths`
  , next :: BTree (Masstree v)
  -- ^ the next layer of nodes for entires with lengths > 8
  }

lookup :: Bytes -> Masstree v -> Maybe v
lookup k t@Masstree{next} = case unconsU64 k of
  Left (padded, len) -> lookupHere t padded len
  Right (prefix, keyRest) -> lookup keyRest =<< BTree.lookup next prefix

insert :: Masstree v -> Bytes -> v -> Masstree v
insert t k v = case unconsU64 k of
  Left (padded, len) -> insertHere t padded len v
  Right (prefix, keyRest) -> undefined -- TODO BTree.insertWith (\treeRest -> insert treeRest keyRest v)


------------------ Helpers ------------

lookupHere :: Masstree v -> Word64 -> Int -> Maybe v
lookupHere Masstree{keys,lengths,values} k l = go =<< Arr.findIndex (<= k) keys
  where
  go i
    | i < Arr.size keys
    , Arr.index keys i == k
    = case compare l (Arr.index lengths i) of
        LT -> go (i + 1)
        EQ -> Just $ Arr.index values i
        GT -> Nothing
    | otherwise = Nothing

insertHere :: Masstree v -> Word64 -> Int -> v -> Masstree v
insertHere t@Masstree{keys,lengths,values} k l v =
  go $ fromMaybe (Arr.size keys) (Arr.findIndex (<= k) keys)
  where
  go i
    | i < Arr.size keys
    , Arr.index keys i == k
    = case compare l (Arr.index lengths i) of
        LT -> go (i + 1)
        EQ -> t{values = Arr.replaceAt values i v} -- key and length are already equal
        GT -> doInsert i
    | otherwise = doInsert i
  doInsert i = t
    { keys = Arr.primInsertAt keys i k
    , lengths = Arr.primInsertAt lengths i l
    , values = Arr.smallInsertAt values i v
    }

unconsU64 :: Bytes -> Either (Word64, Int) (Word64, Bytes)
unconsU64 bs0 =
  let (prefix, len, rest) = go 0 0 bs0
   in if Bytes.null rest
      then Left (prefix, len)
      else Right (prefix, rest)
  where
  go word 8 bs = (word, 8, bs)
  go word len bs = case Bytes.uncons bs of
    Nothing ->
      let word' = word `unsafeShiftL` (8 - len)
       in (word', len, Bytes.empty)
    Just (b, bs') ->
      let word' = (word `unsafeShiftL` 8) .|. fromIntegral @Word8 @Word64 b
       in go word' (len + 1) bs'
