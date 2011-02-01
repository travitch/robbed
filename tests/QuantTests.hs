import System.Random
import Prelude hiding (and, or)

import Data.ROBDD.Strict
import Data.ROBDD.Strict.Visualization

makeFormula :: [Bool] -> [ROBDD] -> ROBDD
makeFormula ops (var:vars) =
  foldr combine var (zip vars ops)
  where combine (v, op) f =
          if op then and f v else or f v
makeFormula ops _ = error "Need at least one var"

main :: IO ()
main = do
  g <- getStdGen
  let rs = randoms g
      (rs1, rs2) = splitAt 100 rs
      logicVars = take 70 $ map makeVar [0..]
      f1 = makeFormula rs1 logicVars
      f2 = makeFormula rs2 logicVars
      f3 = and f1 f2
      f4 = exist f3 16
      f5 = applyExists (&&) f1 f2 [16]
      dag1 = makeDAG f4
      dag2 = makeDAG f5
      sat = anySat f5

  viewDAG dag1
  viewDAG dag2

  print sat
