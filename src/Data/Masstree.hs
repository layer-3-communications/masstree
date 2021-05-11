{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Masstree
  ( Masstree
  , empty
  , singleton
  , lookup
  , insert
  , insertWith
  , upsert
  , upsertF
  , fromList
  ) where

import Prelude hiding (lookup)

import Control.Monad.ST (ST)
import Data.Bits ((.|.), unsafeShiftL)
import Data.Bytes (Bytes)
import Data.Functor ((<&>))
import Data.Functor.Identity (runIdentity)
import Data.Masstree.BTree (BTree)
import Data.Maybe (fromMaybe)
import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Word (Word8,Word64)

import qualified Data.Bytes as Bytes
import qualified Data.Foldable as Foldable
import qualified Data.Masstree.BTree as BTree
import qualified Data.Masstree.Utils as Arr
import qualified Data.Primitive.Contiguous as Arr


data Masstree v = TrieNode
  { lengths :: PrimArray Int
  -- ^ An nth-layer (zero-indexed) node of a masstree contains the values for
  -- all keys with lengths in [8*n, 8*n+8) bytes.
  -- Therefore, we need to know the actual number of bytes (0-7) which were
  -- present in the next-higher layer.
  -- INVARIANT: parallels `values`
  -- INVARIANT: the root has empty `lengths`
  , values :: SmallArray v
  -- ^ values at this node
  -- INVARIANT: parallels `lengths`
  -- INVARIANT: the root has empty `values`
  , next :: BTree (Masstree v)
  -- ^ the next layer of nodes for entires with lengths >= 8
  }
  -- TODO I think it will be very common that there will only be one length at a node (since different lengths can only add spare null bytes), so make a special singleton node; or would that not really save much, given that a singleton node will just hold the same data as the length-1 arrays?
  -- TODO for a run of `8*l` bytes compress layers

empty :: Masstree v
empty = TrieNode
  { lengths = Arr.empty
  , values = Arr.empty
  , next = BTree.empty
  }

singleton :: Bytes -> v -> Masstree v
singleton k v = case unconsU64 k of
  Left (padded, len) ->
    empty{ next = BTree.singleton padded (insertHere len v empty) }
  Right (prefix, keyRest) ->
    empty{ next = BTree.singleton prefix (singleton keyRest v) }


lookup :: Bytes -> Masstree v -> Maybe v
lookup k TrieNode{next} = case unconsU64 k of
  Left (padded, len) -> lookupHere len =<< BTree.lookup padded next
  Right (prefix, keyRest) -> lookup keyRest =<< BTree.lookup prefix next

insert :: Bytes -> v -> Masstree v -> Masstree v
insert = insertWith const

insertWith :: (v -> v -> v) -> Bytes -> v -> Masstree v -> Masstree v
insertWith f k v = upsert (maybe v (flip f v)) k

upsert :: (Maybe v -> v) -> Bytes -> Masstree v -> Masstree v
upsert f k = runIdentity . upsertF (pure . f) k

-- Note: In theory, this should only require a 'Functor' constraint, not 'Monad'.
-- Unfortunately, it is difficult to get good guarantees about thunk leaks without
-- using 'Monad'.
upsertF :: (Monad f) => (Maybe v -> f v) -> Bytes -> Masstree v -> f (Masstree v)
upsertF f k t@TrieNode{next} = case unconsU64 k of
  Left (padded, len) -> (\next' -> t{next = next'}) <$>
    BTree.upsertF (upsertHereF f len . fromMaybe empty) padded next
  Right (prefix, keyRest) -> (\next' -> t{next = next'}) <$>
    BTree.upsertF recurse prefix next
    where
    recurse (Just treeRest) = upsertF f keyRest treeRest
    recurse Nothing = singleton keyRest <$> f Nothing

-- | Build a Masstree from a list of key-value pairs.
fromList :: [(Bytes,v)] -> Masstree v
fromList = Foldable.foldl' (\acc (k,v) -> insert k v acc) empty

------------------ Helpers ------------

-- assuming the padded key was found in the above layer,
-- use the key's leftover length to lookup the correct value at this node
lookupHere :: Int -> Masstree v -> Maybe v
lookupHere l TrieNode{lengths,values} =
  Arr.index values <$> Arr.findIndex (== l) lengths

-- add a value at this node
-- since the padded contents of the key appear at the next-higher layer,
-- we need only the leftover length of the key
insertHere :: Int -> v -> Masstree v -> Masstree v
insertHere l v = runIdentity . upsertHereF (const (pure v)) l

upsertHereF :: (Functor f) => (Maybe v -> f v) -> Int -> Masstree v -> f (Masstree v)
{-# INLINABLE upsertHereF #-}
{-# SPECIALIZE upsertHereF :: (Maybe v -> ST s v) -> Int -> Masstree v -> ST s (Masstree v) #-}
upsertHereF f l t@TrieNode{lengths,values} = case Arr.findIndex (<= l) lengths of
  Just i
    | Arr.index lengths i == l ->
      f (Just $ Arr.index values i) <&> \v ->
        t { values = Arr.replaceAt values i v }
    | otherwise -> f Nothing <&> \v ->
      t { lengths = Arr.primInsertAt lengths i l
        , values = Arr.smallInsertAt values i v
        }
  Nothing -> f Nothing <&> \v ->
    t { lengths = Arr.primInsertAt lengths (Arr.size lengths) l
      , values = Arr.smallInsertAt values (Arr.size values) v
      }

-- split up to eight bytes off
-- if less that eight bytes were found, pad with zeros on the end
-- and report the length in the Left case
unconsU64 :: Bytes -> Either (Word64, Int) (Word64, Bytes)
unconsU64 bs0 = go 0 0 bs0
  where
  go word 8 bs = Right (word, bs)
  go word len bs = case Bytes.uncons bs of
    Nothing ->
      let word' = word `unsafeShiftL` (8 - len)
       in Left (word', len)
    Just (b, bs') ->
      let word' = (word `unsafeShiftL` 8) .|. fromIntegral @Word8 @Word64 b
       in go word' (len + 1) bs'
