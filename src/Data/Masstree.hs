{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Masstree where

import Prelude hiding (lookup)

import Data.Primitive (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Masstree.BTree (BTree)

import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.Utils as Arr


data Masstree v = Masstree
  { lengths :: PrimArray Int
  -- ^ lengths of entries at this node (1-8); parallels `entries`
  , entries :: SmallArray v
  -- ^ entries with lengths 1-8; parallels `lengths`
  , next :: BTree (Masstree v)
  -- ^ the next layer of nodes for entires with lengths > 8
  }
