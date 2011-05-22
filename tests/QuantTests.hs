import Test.Framework ( defaultMain, testGroup )
import Test.Framework.Providers.HUnit
import Test.HUnit

import qualified Data.ROBDD.Strict as BDD

main :: IO ()
main = defaultMain tests

-- tests :: [Test]
tests = [ testGroup "Tautologies" [ testCase "taut1" test_taut1
                                  , testCase "taut2" test_taut2
                                  ]
        , testGroup "Contradictions" [ testCase "contra1" test_contra1
                                     ]
        ]

test_taut1 = assertEqual "x[1] || x[2] ?? x[1] / True" (BDD.restrict bdd 1 True) BDD.makeTrue
  where
    bdd = (BDD.makeVar 1) `BDD.or` (BDD.makeVar 2)

test_taut2 = assertEqual "x[1] || !x[1]" bdd BDD.makeTrue
  where
    bdd = (BDD.makeVar 1) `BDD.or` BDD.neg (BDD.makeVar 1)

test_contra1 = assertEqual "x[1] && !x[1]" bdd BDD.makeFalse
  where
    bdd = (BDD.makeVar 1) `BDD.and` BDD.neg (BDD.makeVar 1)