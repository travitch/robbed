import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit
import Test.HUnit

import Data.Bool.SimpleFormula
import Data.ROBDD.Strict (ROBDD)
import qualified Data.ROBDD.Strict as BDD

binop :: (ROBDD -> ROBDD -> ROBDD) -> Formula -> Formula -> ROBDD
binop op f1 f2 = (formulaToBDD f1) `op` (formulaToBDD f2)

formulaToBDD :: Formula -> ROBDD
formulaToBDD (Var i) = BDD.makeVar i
formulaToBDD (Not f) = BDD.neg (formulaToBDD f)
formulaToBDD (And f1 f2) = binop BDD.and f1 f2
formulaToBDD (Xor f1 f2) = binop BDD.xor f1 f2
formulaToBDD (Or f1 f2) = binop BDD.or f1 f2
formulaToBDD (Impl f1 f2) = binop BDD.impl f1 f2
formulaToBDD (BiImpl f1 f2) = binop BDD.biimpl f1 f2

mkBDD :: String -> ROBDD
mkBDD = (either (error . show) formulaToBDD) . parseString

main :: IO ()
main = defaultMain tests

-- tests :: [Test]
tests = [ testGroup "Tautologies" [ testCase "taut1" test_taut1
                                  , testCase "taut2" test_taut2
                                  ]
        , testGroup "Contradictions" [ testCase "contra1" test_contra1
                                     ]
        ]

test_taut1 = assertEqual (f ++ " ?? x[1] / True") (BDD.restrict bdd 1 True) BDD.makeTrue
  where
    f = "x[1] | x[2]"
    bdd = mkBDD f

test_taut2 = assertEqual f (mkBDD f) BDD.makeTrue
  where f = "x[1] | !x[1]"

test_contra1 = assertEqual f (mkBDD f) BDD.makeFalse
  where f = "x[1] & !x[1]"
