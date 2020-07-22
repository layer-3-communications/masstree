{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Monad (when)
import Data.Masstree.BTree (BTree)
import Data.Maybe (isJust)
import Data.Proxy (Proxy(Proxy))
import Data.Semigroup (Sum,First)
import Data.Word (Word8,Word64)
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.QuickCheck ((===))

import qualified Data.List as List
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
    [ TQC.testProperty "order-invariant" $ \(Keys xs) ->
        let ys = map (\x -> (fromIntegral x,x)) xs in
        checkOrderInvariant (BTree.fromList ys)
    , TQC.testProperty "height-invariant" $ \(Keys xs) ->
        let ys = map (\x -> (fromIntegral x,x)) xs in
        checkHeightInvariant (BTree.fromList ys)
    , lawsToTest (QCC.monoidLaws (Proxy :: Proxy (BTree Integer)))
    , TQC.testProperty "fromList-toList-keys" $ \(Keys xs) ->
        let ys = map (\x -> (fromIntegral x,x)) xs in
        sortList (map fst ys)
        ===
        map fst (BTree.toList (BTree.fromList ys))
    , TQC.testProperty "fromList-toList" $ \(Keys xs) ->
        let ys = map (\x -> (fromIntegral x,x)) xs in
        Map.toList (Map.fromList ys)
        ===
        BTree.toList (BTree.fromList ys)
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
             | ksz == 0 -> error "Impossible key size"
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
             | sz == 1 -> [BTree.empty]
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

checkHeightInvariant :: BTree v -> Bool
checkHeightInvariant = isJust . go
  where
  go :: BTree v -> Maybe Int
  go = \case
    BTree.Leaf{} -> Just 0
    BTree.Branch{children} -> case PM.sizeofSmallArray children of
      -- Returning zero when there are no children is kind of
      -- a trick. This should only happen when the root is empty.
      0 -> Just 0
      _ -> do
        hs <- traverse go children
        let h0 = PM.indexSmallArray hs 0
        if (Arr.all (\h -> h == h0) hs)
          then Just h0
          else Nothing

checkOrderInvariant :: BTree v -> Bool
checkOrderInvariant = go where
  go = \case
    BTree.Leaf{keys} -> isSorted keys
    BTree.Branch{keys,children} ->
      all go children
      &&
      isSorted keys
      &&
      checkOrderInvariantChildren keys children

checkOrderInvariantChildren :: PM.PrimArray Word64 -> PM.SmallArray (BTree v) -> Bool
checkOrderInvariantChildren keys children
  | ksz + 1 /= csz = False
  | otherwise =
      Arr.all
        (\k -> k >= PM.indexPrimArray keys (ksz - 1))
        (rootKeys (PM.indexSmallArray children ksz))
      &&
      Arr.all
        (\k -> k < PM.indexPrimArray keys 0)
        (rootKeys (PM.indexSmallArray children 0))
      &&
      go (ksz - 2) (ksz - 1) (ksz - 1)
  where
  ksz = Arr.size keys
  csz = Arr.size children
  go !ixKeyLo !ixKeyHi !ixChild = if ixKeyLo == (-1)
    then True
    else
      Arr.all
        (\k -> k >= PM.indexPrimArray keys ixKeyLo)
        (rootKeys (PM.indexSmallArray children ixChild))
      &&
      Arr.all
        (\k -> k < PM.indexPrimArray keys ixKeyHi)
        (rootKeys (PM.indexSmallArray children ixChild))
      &&
      go (ixKeyLo - 1) (ixKeyHi - 1) (ixChild - 1)

rootKeys :: BTree v -> PM.PrimArray Word64
rootKeys = \case
  BTree.Leaf{keys} -> keys
  BTree.Branch{keys} -> keys

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

-- This is only here to help GHC give us more accurate profiling information.
-- For some reason, either cabal or GHC cannot be coaxed into showing the
-- amount of time spent in functions in Data.List.
sortList :: [Word64] -> [Word64]
{-# noinline sortList #-}
sortList xs = List.nub (List.sort xs)

newtype Keys = Keys { unKeys :: [Word64] }
  deriving newtype (Show)

instance TQC.Arbitrary Keys where
  arbitrary = Keys <$> TQC.vectorOf 100 (TQC.choose (0,200))
  shrink = map Keys . TQC.shrinkList (\_ -> []) . unKeys
