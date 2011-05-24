import Control.Applicative
import Data.List (mapAccumL)
import Test.Framework ( defaultMain, testGroup, Test )
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.HUnit hiding (Test, test)
import Test.QuickCheck

import Data.Bool.SimpleFormula
import Data.ROBDD.Strict (ROBDD)
import qualified Data.ROBDD.Strict as BDD

-- The subtree is a monadic value and not a shared value - different
-- subtrees are produced.
arbitraryFormula :: Gen Formula
arbitraryFormula = sized formula

formula ::  Int -> Gen Formula
formula sz = formula' sz
  where
    formula' 0 = Var <$> choose (0, sz)
    formula' n = oneof [ Var <$> choose (0, sz)
                       , Not <$> st
                       , And <$> st <*> st
                       , Xor <$> st <*> st
                       , Or <$> st <*> st
                       , Impl <$> st <*> st
                       , BiImpl <$> st <*> st
                       ]
      where
        st = formula' (n `div` 2)

instance Arbitrary Formula where
  arbitrary = arbitraryFormula


newtype ReplaceMap = RM [(Int, Int)]
instance Arbitrary ReplaceMap where
  arbitrary = arbitraryReplaceMap

arbitraryReplaceMap :: Gen ReplaceMap
arbitraryReplaceMap = sized replaceMap
  where
    replaceMap :: Int -> Gen ReplaceMap
    replaceMap sz = RM <$> (vectorOf sz ((,) <$> choose (0, sz) <*> choose (0, sz)))

newtype VariableAssignment = VA [(Int, Bool)]
instance Arbitrary VariableAssignment where
  arbitrary = arbitraryVariableAssignment

arbitraryVariableAssignment :: Gen VariableAssignment
arbitraryVariableAssignment = sized va
  where
    va sz = VA <$> (vectorOf sz ((,) <$> choose (0, sz) <*> elements [True, False]))

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
        , testGroup "Properties" [ testProperty "bddEq" prop_bddEq
                                 , testProperty "satValid" prop_satIsValid
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

-- replaceTests :: [Assertion]
-- replaceTests = [ testReplacement "(x[1] & x[2]) | (x[3] ^ x[4]) & (x[2] -> x[5])"
--                    [(3, 11), (1, 16)]
--                ]
--   where
--     testReplacement f rep = assertEqual f
--       where
--         bbd = mkBDD f
--         bdd' = replace bdd rep

test_contra1 = assertEqual f (mkBDD f) BDD.makeFalse
  where f = "x[1] & !x[1]"

-- unsparsifyAssignment :: [(Int, Bool)]

prop_satIsValid :: Formula -> Bool
prop_satIsValid f = case sol of
  Just _ -> defTrue == True && defFalse == True
  Nothing -> True
  where
    bdd = formulaToBDD f
    sol :: Maybe [(Int, Bool)]
    sol = BDD.anySat bdd
    sol' = maybe (error $ show sol) id sol
    defTrue = interpretFormulaDefault True f sol'
    defFalse = interpretFormulaDefault False f sol'

-- prop_simpleAssign :: (Formula, VariableAssignment) -> Bool
-- prop_simpleAssign (f, VA assign) = x
--   where
--     bdd = formulaToBDD f
--     val = BDD.restrictAll bdd assign
--     defTrue = interpretFormulaDefault True f assign
--     defFalse = interpretFormulaDefault False f assign

-- prop_replaceEquiv :: (Formula, ReplaceMap) -> Bool
-- prop_replaceEquiv (f, RM repl) = undefined
--   where
--     bdd0 = formulaToBDD f
--     bdd' = BDD.replace bdd0 repl

prop_bddEq :: Formula -> Bool
prop_bddEq f = bdd == bdd
  where
    bdd = formulaToBDD f
