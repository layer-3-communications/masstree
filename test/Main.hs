{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Monad (when)
import Data.Masstree.BTree (BTree)
import Data.Proxy (Proxy(Proxy))
import Data.Semigroup (Sum,First)
import Data.Word (Word8,Word64)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.QuickCheck ((===))

import qualified Data.Map.Strict as Map
import qualified Data.Primitive as PM
import qualified Data.Primitive.Contiguous as Arr
import qualified Data.Masstree.BTree as BTree
import qualified Test.QuickCheck.Classes.Base as QCC
import qualified Test.Tasty.QuickCheck as TQC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests"
  [ testGroup "BTree"
    [ TQC.testProperty "order-invariant" $ \(xs :: [(Word64,Word8)]) ->
        checkOrderInvariant (BTree.fromList xs)
    , lawsToTest (QCC.monoidLaws (Proxy :: Proxy (BTree Integer)))
    , TQC.testProperty "fromList-toList" $ \(xs :: [(Word64,Word8)]) ->
        Map.toList (Map.fromList xs)
        ===
        BTree.toList (BTree.fromList xs)
    ]
  ]

lawsToTest :: QCC.Laws -> TestTree
lawsToTest (QCC.Laws name pairs) =
  testGroup name (map (uncurry TQC.testProperty) pairs)

instance TQC.Arbitrary v => TQC.Arbitrary (BTree v) where
  arbitrary = BTree.fromList <$> TQC.arbitrary
  shrink = \case
    BTree.Branch{keys,children} -> 
      let ksz = Arr.size keys
          csz = Arr.size children
       in if | ksz + 1 /= csz ->
                 error "Keys and children had disagreeing lengths. Dieing."
             | ksz == 1 -> []
             | otherwise ->
                 [ BTree.Branch
                     { keys = Arr.clone keys 1 (ksz - 1)
                     , children = Arr.clone children 1 (csz - 1)
                     }
                 , BTree.Branch
                     { keys = Arr.clone keys 0 (ksz - 1)
                     , children = Arr.clone children 0 (csz - 1)
                     }
                 ]
    BTree.Leaf{keys,values} ->
      let ksz = Arr.size keys
          vsz = Arr.size values
          sz = ksz
       in if | ksz /= vsz ->
                 error "Keys and values had different lengths. Dieing."
             | sz == 0 -> []
             | otherwise -> 
                 [ BTree.Leaf
                     { keys = Arr.clone keys 1 (sz - 1)
                     , values = Arr.clone values 1 (sz - 1)
                     }
                 , BTree.Leaf
                     { keys = Arr.clone keys 0 (sz - 1)
                     , values = Arr.clone values 0 (sz - 1)
                     }
                 ]

-- This does not totally check the order invariant yet.
-- TODO: finish this.
checkOrderInvariant :: BTree v -> Bool
checkOrderInvariant = go where
  go = \case
    BTree.Leaf{keys} -> isSorted keys
    BTree.Branch{children} -> all go children

isSorted :: PM.PrimArray Word64 -> Bool
isSorted xs = if sz < 1
  then True
  else go (PM.indexPrimArray xs (sz - 1)) (sz - 2)
  where
  sz = PM.sizeofPrimArray xs
  go !successor !ix = if ix == (-1)
    then True 
    else
      let element = PM.indexPrimArray xs ix
       in if element < successor
            then go element (ix - 1)
            else False
