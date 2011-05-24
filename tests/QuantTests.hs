import Data.List (mapAccumL)
import Test.Framework ( defaultMain, testGroup, Test )
import Test.Framework.Providers.HUnit
import Test.HUnit hiding (Test, test)

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

tests :: [Test]
tests = [ testGroup "Tautologies" (casifyTests "taut" tautologyTests)
        , testGroup "Contradictions" [ testCase "contra1" test_contra1
                                     ]
        ]

casifyTests :: String -> [Assertion] -> [Test]
casifyTests pfx = snd . (mapAccumL casify 0)
  where
    casify idx test = (idx + 1, testCase (pfx ++ show idx) test)

-- Most of these are simple examples taken from Wikipedia
tautologyTests :: [Assertion]
tautologyTests = [ testTautology "x[1] | !x[1]" -- Law of the excluded middle
                 , testTautology "x[1] -> x[1]"
                 , testTautology "(x[1] -> x[2]) <-> (!x[2] -> !x[1])" -- Contrapositive
                 , testTautology "((!x[1] -> x[2]) & (!x[1] -> !x[2])) -> x[1]" -- reductio ad absurdum
                 , testTautology "!(x[1] & x[2]) <-> (!x[1] | !x[2])" -- de Morgan's Law
                 , testTautology "((x[1] -> x[2]) & (x[2] -> x[3])) -> (x[1] -> x[3])" -- Syllogism
                 , testTautology "((x[1] | x[2]) & (x[1] -> x[3]) & (x[2] -> x[3])) -> x[3]" -- Proof by cases
                 , testTautology (concat ["(", big1, ") -> (", big1, ")"])
                 ]
  where
    testTautology f = assertEqual f (mkBDD f) BDD.makeTrue
    big1 = "x[1] & x[2] & x[3] | !x[4] ^ x[5] & x[6] <-> x[7]"

test_contra1 = assertEqual f (mkBDD f) BDD.makeFalse
  where f = "x[1] & !x[1]"
