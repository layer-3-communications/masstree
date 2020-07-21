module Data.Masstree.ArrayList where

import Control.Monad.ST (runST)
import Data.Primitive (Prim, PrimArray)

import qualified Data.Primitive as PM

type ArrayList a = PrimArray a



-- FIXME move to utils before using for masstree
-- split the source array in half, then insert the value in one side or the other
splitInsert :: Prim a => ArrayList a -> Int -> a -> (ArrayList a, ArrayList a)
splitInsert src i x = runST $ do
  let len0 = PM.sizeofPrimArray src
      (lenL, lenR) = case (len0 + 1) `divMod` 2 of
        (0, l) -> (l, l)
        (_, l) -> (l + 1, l)
  dstL <- PM.newPrimArray lenL
  dstR <- PM.newPrimArray lenR
  if (i < lenL)
    then do
      PM.copyPrimArray dstL 0 src 0 i
      PM.writePrimArray dstL i x
      PM.copyPrimArray dstL (i + 1) src i (lenL - i - 1)
      PM.copyPrimArray dstR 0 src lenL lenR
    else do
      let i' = i - lenL
      PM.copyPrimArray dstL 0 src 0 lenL
      PM.copyPrimArray dstR 0 src lenL i'
      PM.writePrimArray dstR i' x
      PM.copyPrimArray dstR (i' + 1) src i (lenR - i' - 1)
  arrL <- PM.unsafeFreezePrimArray dstL
  arrR <- PM.unsafeFreezePrimArray dstR
  pure (arrL, arrR)
