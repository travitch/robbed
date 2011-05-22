import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit
import Test.HUnit

import qualified Data.ROBDD.Strict as BDD

main :: IO ()
main = defaultMain tests

-- tests :: [Test]
tests = [ testGroup "Tautologies" [
             testCase "taut1" test_taut1
             ]
        ]

test_taut1 = assertEqual "x[1] || x[2] ?? x[1] / True" (BDD.restrict bdd 1 True) BDD.makeTrue
  where
    bdd = (BDD.makeVar 1) `BDD.or` (BDD.makeVar 2)

-- import System.Random
-- import Prelude hiding (and, or)

-- import Data.ROBDD.Strict
-- import Data.ROBDD.Strict.Visualization

-- makeFormula :: [Bool] -> [ROBDD] -> ROBDD
-- makeFormula ops (var:vars) =
--   foldr combine var (zip vars ops)
--   where combine (v, op) f =
--           if op then and f v else or f v
-- makeFormula ops _ = error "Need at least one var"

-- main :: IO ()
-- main = do
--   g <- getStdGen
--   let rs = randoms g
--       (rs1, rs2) = splitAt 100 rs
--       logicVars = take 100 $ map makeVar [0..]
--       f1 = makeFormula rs1 logicVars
--       f2 = makeFormula rs2 logicVars
--       f3 = and f1 f2
--       f4 = exist f3 16
--       f5 = applyExists (&&) f1 f2 [16]
--       dag1 = makeDAG f4
--       dag2 = makeDAG f5
--       sat = anySat f5

--   viewDAG dag1
--   viewDAG dag2

--   print sat
