{-# language NumericUnderscores #-}

import Data.Word (Word64)
import Data.Compact (compactSized, compactSize)
import Data.Foldable (foldlM)
import Data.List (unfoldr)
import System.Random (mkStdGen,uniformR)

import qualified Data.Masstree.BTree as BTree
import qualified Data.Map.Strict as Map

main :: IO ()
main = do
  measure "50000-w64-unit" pairs50000

measure :: String -> [(Word64,())] -> IO ()
measure name pairs = do
  putStrLn name
  let bt = BTree.fromList pairs
  let mp = Map.fromList pairs
  heapBTree <- estimateHeapUse bt
  heapMap <- estimateHeapUse mp
  putStrLn ("  BTree:          " ++ show heapBTree ++ " bytes")
  putStrLn ("  Containers Map: " ++ show heapMap ++ " bytes")

estimateHeapUse :: a -> IO Word
estimateHeapUse a = foldlM
  ( \lo i -> do
    w <- compactSized (i * 2000) True a >>= compactSize
    pure (min lo w)
  ) maxBound [1..50]

pairs50000 :: [(Word64,())]
{-# noinline pairs50000 #-} 
pairs50000 = map
  (\x -> (x,()))
  (take 50000 (unfoldr (Just . uniformR (0, 1_000_000_000)) (mkStdGen 9652364)))
