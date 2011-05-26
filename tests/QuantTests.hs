import Control.Applicative
import Data.List (mapAccumL, foldl')
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust, isJust)
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

maxVars :: Int
maxVars = 30

formula ::  Int -> Gen Formula
formula sz = formula' sz'
  where
    sz' = min maxVars sz
    formula' 0 = Var <$> choose (0, sz')
    formula' n = oneof [ Var <$> choose (0, sz')
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
                   deriving (Show)
instance Arbitrary ReplaceMap where
  arbitrary = arbitraryReplaceMap

arbitraryReplaceMap :: Gen ReplaceMap
arbitraryReplaceMap = sized replaceMap
  where
    replaceMap :: Int -> Gen ReplaceMap
    replaceMap sz =
      let sz' = min sz maxVars
          newNameGen = choose (maxVars + 200, maxVars + 200 + sz')
          initNameGen = choose (0, sz')
      in RM <$> vectorOf sz' ((,) <$> initNameGen <*> newNameGen)

newtype VariableAssignment = VA [(Int, Bool)]
                           deriving (Show)
instance Arbitrary VariableAssignment where
  arbitrary = arbitraryVariableAssignment

arbitraryVariableAssignment :: Gen VariableAssignment
arbitraryVariableAssignment = sized va
  where
    va sz = VA <$> (vectorOf sz ((,) <$> choose (0, sz) <*> elements [True, False]))

newtype VariableList = VL [Int]
                     deriving (Show)
instance Arbitrary VariableList where
  arbitrary = arbitraryVariableList

arbitraryVariableList :: Gen VariableList
arbitraryVariableList = sized vl
  where
    vl sz = VL <$> vectorOf sz (choose (0, sz))

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
                                 , testProperty "deMorgan" prop_deMorgan
                                 , testProperty "idempotentNegate" prop_bddNegIdemp
                                 , testProperty "satValid" prop_satIsValid
                                 , testProperty "satValidSelf" prop_satIsValidSelf
                                 , testProperty "resAndResAll" prop_restrictAndRestrictAllAgree
                                 , testProperty "existAndExistAll" prop_existAndApplyExistAgree
                                 , testProperty "restrictUnordered" prop_restrictUnordered
                                 , testProperty "renameEquiv" prop_replaceEquiv
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

-- Simple contradiction test
test_contra1 :: Assertion
test_contra1 = assertEqual f (mkBDD f) BDD.makeFalse
  where f = "x[1] & !x[1]"

-- | Ensure that the satisfying assignment returned by anySat actually
-- satisfies the formula (comparing against the formula interpreter).
-- This property interprets the formula twice - once with each default
-- value.  This is because 'interpretFormula' requires all variables
-- to have assignments but the satisfying solution from the BDD
-- probably won't have all variables assigned.
prop_satIsValid :: Formula -> Property
prop_satIsValid f =
  isJust sol ==> defTrue == True && defFalse == True
  where
    bdd = formulaToBDD f
    sol :: Maybe [(Int, Bool)]
    sol = BDD.anySat bdd
    sol' = maybe (error $ show sol) id sol
    defTrue = interpretFormulaDefault True f sol'
    defFalse = interpretFormulaDefault False f sol'

-- | Substituting in the solution returned by anySat should result in
-- a tautology.
prop_satIsValidSelf :: Formula -> Property
prop_satIsValidSelf f =
  isJust sol ==> BDD.restrictAll bdd (fromJust sol) == BDD.makeTrue
  where
    bdd = formulaToBDD f
    sol = BDD.anySat bdd

-- | Ensure that restrictAll and repeated applications of restrict
-- agree and produce the same result.
prop_restrictAndRestrictAllAgree :: (Formula, VariableAssignment) -> Bool
prop_restrictAndRestrictAllAgree (f, VA assign) = resAll == resIncr
  where
    assign' = M.toList $ M.fromList $ take 5 assign
    -- ^ Only take a few - this could be expensive.  Also uniquify
    -- based on the keys (variables).  Duplicate entries with
    -- different bool values can lead to false-positive errors due to
    -- the way restrictAll manages its assignments.
    bdd = formulaToBDD f
    resAll = BDD.restrictAll bdd assign'
    resIncr = foldl' incrRestrict bdd assign'
    incrRestrict b (var, val) = BDD.restrict b var val

-- | Ensure that the order of variable restriction does not affect
-- results.
prop_restrictUnordered :: (Formula, VariableAssignment) -> Bool
prop_restrictUnordered (f, VA assign) = bdd1 == bdd2
  where
    assign' = M.toList $ M.fromList $ take 10 assign
    assign1 = assign'
    assign2 = reverse assign'
    bdd = formulaToBDD f
    bdd1 = BDD.restrictAll bdd assign1
    bdd2 = BDD.restrictAll bdd assign2

-- | Compare the results of applyExists (to existentially quantify a
-- set of variables) to the result obtained by repeated applications
-- of the simpler exist function.  They should agree.
prop_existAndApplyExistAgree :: (Formula, VariableList) -> Bool
prop_existAndApplyExistAgree (f, VL vs) = exAll == exIncr
  where
    vs' = take 5 vs
    bdd = formulaToBDD f
    exAll = BDD.applyExists const bdd bdd vs'
    exIncr = foldl' BDD.exist bdd vs'

-- | The new names for variables need to be unique (e.g., [(1, 50),
-- (5, 50)] is an error).  This function filters out invalid pairings.
fixReplacementMap :: ReplaceMap -> [(Int, Int)]
fixReplacementMap (RM repl) =
  zip (S.toList $ S.fromList srcs) (S.toList $ S.fromList dsts)
  where
    (srcs, dsts) = unzip repl

-- | Ensure replace actually works by replacing some variables and
-- performing an equivalent variable restriction on the replaced
-- variables.  This is a partial test.
prop_replaceEquiv :: (Formula, ReplaceMap, [Bool]) -> Property
prop_replaceEquiv (f, repl, assignVals) =
  (length assignVals >= length repl') ==>
  collect (length repl') $
  BDD.restrictAll bdd origAssign == BDD.restrictAll bdd' renamedAssign
  where
    repl' = fixReplacementMap repl
    (origVars, newVars) = unzip repl'
    origAssign = zip origVars assignVals
    renamedAssign = zip newVars assignVals
    bdd = formulaToBDD f
    bdd' = BDD.replace bdd repl'

-- | Test to ensure deMorgan's law always holds.
prop_deMorgan :: (Formula, Formula) -> Bool
prop_deMorgan (f1, f2) =
  BDD.neg (b1 `BDD.and` b2) == (BDD.neg b1) `BDD.or` (BDD.neg b2)
  where
    b1 = formulaToBDD f1
    b2 = formulaToBDD f2

-- | Double negation should be a no-op
prop_bddNegIdemp :: Formula -> Bool
prop_bddNegIdemp f = bdd == BDD.neg (BDD.neg bdd)
  where
    bdd = formulaToBDD f

-- | A BDD should always be equal to itself.
prop_bddEq :: Formula -> Bool
prop_bddEq f = bdd == bdd
  where
    bdd = formulaToBDD f
