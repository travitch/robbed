module Data.ROBDD.Strict ( BDD(..)
                         , ROBDD(..)
                         , apply
                         , applyExists
                         , applyForAll
                         , applyUnique
                         , restrict
                         , restrictAll
                         , anySat
                         , makeVar
                         , makeTrue
                         , makeFalse
                         , and
                         , or
                         , xor
                         , impl
                         , biimpl
                         , nand
                         , nor
                         , neg
                         , exist
                         , forAll
                         , unique
                         ) where

import Prelude hiding (and, or)
import Control.Monad.State
import qualified Data.HamtMap as M
import Data.Hashable
import qualified Data.HashSet as S

import Data.ROBDD.Strict.Types
import Data.ROBDD.BooleanFunctions

makeTrue :: ROBDD
makeTrue = ROBDD M.empty [] One
makeFalse :: ROBDD
makeFalse = ROBDD M.empty [] Zero
makeVar :: Var -> ROBDD
makeVar v
  | v >= 0 = ROBDD M.empty [] bdd
  | otherwise = error "Variable numbers must be >= 0"
  where bdd = BDD Zero v One 0


-- Types used internally; these are for a State monad that tracks memo
-- tables and revmap updates.
data BDDState a = BDDState { bddRevMap :: RevMap
                           , bddIdSource :: [Int]
                           , bddMemoTable :: Map a BDD
                           }

-- Start IDs at 2, since Zero and One are conceptually taken
emptyBDDState :: (Eq a, Hashable a) => BDDState a
emptyBDDState = BDDState { bddRevMap = M.empty
                         , bddIdSource = [0..]
                         , bddMemoTable = M.empty
                         }

type BDDContext a b = State (BDDState a) b

revLookup :: Var -> BDD -> BDD -> RevMap -> (Maybe BDD)
revLookup v leftTarget rightTarget revMap = do
  M.lookup (v, nodeUID leftTarget, nodeUID rightTarget) revMap

-- Create a new node for v with the given high and low edges.
-- Insert it into the revMap and return it.
revInsert :: Var -> BDD -> BDD -> BDDContext a BDD
revInsert v lowTarget highTarget = do
  s <- get
  let revMap = bddRevMap s
      (nodeId:rest) = bddIdSource s
      revMap' = M.insert (v, nodeUID lowTarget, nodeUID highTarget) newNode revMap
      newNode = BDD lowTarget v highTarget nodeId
  put $ s { bddRevMap = revMap'
          , bddIdSource = rest }

  return newNode

-- A helper to memoize BDD nodes
memoNode :: (Eq a, Hashable a) => a -> BDD -> BDDContext a ()
memoNode key val = do
  s <- get
  let memoTable = bddMemoTable s
      memoTable' = M.insert key val memoTable

  put s { bddMemoTable = memoTable' }

getMemoNode :: (Eq a, Hashable a) => a -> BDDContext a (Maybe BDD)
getMemoNode key = do
  s <- get
  let memoTable = bddMemoTable s

  return $ M.lookup key memoTable

memoize :: (Eq a, Hashable a) => a -> State (BDDState a) BDD -> State (BDDState a) BDD
memoize uid act = do
  mem <- getMemoNode uid
  case mem of
    Just node -> return node
    Nothing -> act


and :: ROBDD -> ROBDD -> ROBDD
and = apply (&&)

or :: ROBDD -> ROBDD -> ROBDD
or = apply (||)

xor :: ROBDD -> ROBDD -> ROBDD
xor = apply boolXor

impl :: ROBDD -> ROBDD -> ROBDD
impl = apply boolImpl

biimpl :: ROBDD -> ROBDD -> ROBDD
biimpl = apply boolBiimp

nand :: ROBDD -> ROBDD -> ROBDD
nand = apply boolNotAnd

nor :: ROBDD -> ROBDD -> ROBDD
nor = apply boolNotOr

-- | Existentially quantify a single variable from a BDD
exist :: ROBDD -> Var -> ROBDD
exist bdd var = or (restrict bdd var True) (restrict bdd var False)

-- |
unique :: ROBDD -> Var -> ROBDD
unique bdd var = xor (restrict bdd var True) (restrict bdd var False)

forAll :: ROBDD -> Var -> ROBDD
forAll bdd var = and (restrict bdd var True) (restrict bdd var False)

-- | Construct a new BDD by applying the provided binary operator
-- to the two input BDDs
--
-- Note: the reverse node maps of each input BDD are ignored because
-- we need to build a new one on the fly for the result BDD.
apply :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> ROBDD
apply op (ROBDD _ _ bdd1) (ROBDD _ _ bdd2) =
  let (bdd, s) = runState (applyInner op stdCtxt bdd1 bdd2) emptyBDDState
      -- FIXME: Remove unused bindings in the revmap to allow the
      -- runtime to GC unused nodes
  in ROBDD (bddRevMap s) (bddIdSource s) bdd

type BinBoolFunc = Bool -> Bool -> Bool

-- This is the main implementation of apply, but also re-used for the
-- combined apply/quantify operations.
applyInner :: BinBoolFunc -> EvaluationContext -> BDD -> BDD -> BDDContext (Int, NodeId, NodeId) BDD
applyInner op ctxt bdd1 bdd2 = appBase bdd1 bdd2
  where appBase :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD
        appBase lhs rhs = memoize (ctxt, nodeUID lhs, nodeUID rhs) $ do
          case maybeApply op lhs rhs of
            Just True -> return One
            Just False -> return Zero
            Nothing -> appRec lhs rhs

        appRec :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD
        appRec lhs rhs = do
          (v, l', h') <- applyRecCore appBase lhs rhs
          newNode <- mk v l' h'
          memoNode (ctxt, nodeUID lhs, nodeUID rhs) newNode
          return newNode

maybeApply :: (Bool -> Bool -> Bool) -> BDD -> BDD -> Maybe Bool
maybeApply op lhs rhs = do
  b1 <- toBool lhs
  b2 <- toBool rhs
  return $ b1 `op` b2

toBool :: BDD -> Maybe Bool
toBool One = Just True
toBool Zero = Just False
toBool _ = Nothing

applyRecCore :: (Monad m) => (BDD -> BDD -> m BDD) -> BDD -> BDD -> m (Var, BDD, BDD)
applyRecCore appBase lhs rhs = case lhs `bddCmp` rhs of
  -- Vars are the same, so use high and low of both lhs and rhs as the
  -- sub-problem
  EQ -> do
    newLowNode <- appBase (lowEdge lhs) (lowEdge rhs)
    newHighNode <- appBase (highEdge lhs) (highEdge rhs)
    return (nodeVar lhs, newLowNode, newHighNode)
  -- Var1 is less than var2, so only take the low/high edges of the
  -- lhs
  LT -> do
    newLowNode <- appBase (lowEdge lhs) rhs
    newHighNode <- appBase (highEdge lhs) rhs
    return (nodeVar lhs, newLowNode, newHighNode)

    -- Var1 is greater than v2
  GT -> do
    newLowNode <- appBase lhs (lowEdge rhs)
    newHighNode <- appBase lhs (highEdge rhs)
    return (nodeVar rhs, newLowNode, newHighNode)

type EvaluationContext = Int

stdCtxt :: EvaluationContext
stdCtxt = 1

innerCtxt :: EvaluationContext
innerCtxt = 2

-- This is the main implementation of the combined apply/quantify
-- operators.  They are really all the same except for the
-- quantification operator.
genericApply :: BinBoolFunc -> BinBoolFunc ->
                ROBDD -> ROBDD -> [Var] -> ROBDD
genericApply quantifier op (ROBDD _ _ bdd1) (ROBDD _ _ bdd2) evars =
  let (bdd, s) = runState (appBase bdd1 bdd2) emptyBDDState
  in ROBDD (bddRevMap s) (bddIdSource s) bdd
  where varSet = S.fromList evars
        appBase :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD
        appBase lhs rhs = memoize (stdCtxt, nodeUID lhs, nodeUID rhs) $ do
          case maybeApply op lhs rhs of
            Just True -> return One
            Just False -> return Zero
            Nothing -> appRec lhs rhs
        appRec :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD
        appRec lhs rhs = do
          (v', l', h') <- applyRecCore appBase lhs rhs
          newNode <- case v' `S.member` varSet of
            -- Standard case - we are not projecting out this variable
            -- so just let mk handle creating a new node if necessary
            False -> mk v' l' h'
            -- If this variable is to be quantified out, this magic is
            -- due to McMillan 92; we quantify it out while we are
            -- building the tree via a call to or.  This re-uses the
            -- current BDD context and so does not use the top-level
            -- or, but the underlying machinery
            True -> applyInner quantifier innerCtxt l' h'
          memoNode (stdCtxt, nodeUID lhs, nodeUID rhs) newNode
          return newNode


-- | A variant of apply that existentially quantifies out the provided
-- list of variables on the fly during the bottom-up construction of
-- the result.  This is much more efficient than performing the
-- quantification after the apply.
applyExists :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyExists = genericApply (||)
applyUnique :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyUnique = genericApply boolXor
applyForAll :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyForAll = genericApply (&&)


restrict :: ROBDD -> Var -> Bool -> ROBDD
restrict bdd@(ROBDD _ _ Zero) _ _ = bdd
restrict bdd@(ROBDD _ _ One) _ _ = bdd
restrict (ROBDD revMap idSrc bdd) v b =
  let (r,s) = runState (restrict' bdd) emptyBDDState { bddIdSource = idSrc
                                                     , bddRevMap = revMap
                                                     }
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where restrict' Zero = return Zero
        restrict' One = return One
        restrict' o@(BDD low var high uid) = memoize uid $ do
          case var `compare` v of
            GT -> return o
            LT -> do
              low' <- restrict' low
              high' <- restrict' high
              n <- mk var low' high'
              memoNode uid n
              return n
            EQ -> case b of
              True -> restrict' high
              False -> restrict' low

-- | restrict over a list of variable/value pairs.  This should be
-- more efficient than repeated calls to restrict.
restrictAll :: ROBDD -> [(Var, Bool)] -> ROBDD
restrictAll bdd@(ROBDD _ _ Zero) _ = bdd
restrictAll bdd@(ROBDD _ _ One) _ = bdd
restrictAll (ROBDD revMap idSrc bdd) vals =
  let (r, s) = runState (restrict' bdd) emptyBDDState { bddIdSource = idSrc
                                                      , bddRevMap = revMap
                                                      }
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where valMap = M.fromList vals
        restrict' Zero = return Zero
        restrict' One = return One
        restrict' (BDD low var high uid) = memoize uid $ do
          case var `M.lookup` valMap of
            Just b -> case b of
              True -> restrict' high
              False -> restrict' low
            Nothing -> do
              low' <- restrict' low
              high' <- restrict' high
              n <- mk var low' high'
              memoNode uid n
              return n

-- | negate the given BDD.  This implementation is somewhat more
-- efficient than the naiive translation to BDD -> False.
-- Unfortunately, it isn't as much of an improvement as it could be
-- via destructive updates. FIXME: Implement constant-time negation
-- either via negation arcs or just a flag on the ROBDD structure
neg :: ROBDD -> ROBDD
neg (ROBDD _ _ bdd) =
  -- Everything gets re-allocated so don't bother trying to re-use the
  -- revmap or idsource
  let (r, s) = runState (negate' bdd) emptyBDDState
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where negate' Zero = return One
        negate' One = return Zero
        negate' (BDD low var high uid) = memoize uid $ do
          low' <- negate' low
          high' <- negate' high
          n <- mk var low' high'
          memoNode uid n
          return n

anySat :: ROBDD -> Maybe ([(Var, Bool)])
anySat (ROBDD _ _ Zero) = Nothing
anySat (ROBDD _ _ One) = Just []
-- FIXME: Might need to make sat' strict in the accumulator
anySat (ROBDD _ _ bdd) = Just $ sat' bdd []
  where sat' One acc = acc
        sat' Zero _ = error "anySat should not hit Zero"
        sat' (BDD low v high _) acc =
          case low of
            Zero -> (v, True) : sat' high acc
            _ -> (v, False) : sat' low acc


-- TODO: satCount, allSat

-- | The MK operation.  Re-use an existing BDD node if possible.
-- Otherwise create a new node with the provided NodeId, updating the
-- tables.  This is not exported and just used internally.
mk :: Var -> BDD -> BDD -> BDDContext a BDD
mk v low high = do
  s <- get

  let revMap = bddRevMap s

  if low == high
    then return low -- Inputs identical, re-use
    else case revLookup v low high revMap of
      -- Return existing node
      Just node -> return node
      -- Make a new node
      Nothing -> revInsert v low high


-- Testing stuff


-- main = do
--   let x0 = makeVar 0
--       x1 = makeVar 1
--       x2 = makeVar 2
--       f1 = and x0 x1
--       f2 = or f1 x2
--       f3 = or f2 makeTrue -- tautology
--       f4 = restrict f2 1 False
--       f5 = neg f2
--       dag = makeDAG f5

--   viewDAG dag

-- testQuant = do
--   let [x0, x1, x2, x3] = map makeVar [0, 1, 2, 3]
--       f1 = and x0 x1
--       f2 = and x1 x2
--       f3 = x3
--       f4 = and f2 f3
--       f5 = and f1 f4
--       q1 = exist f5 2
--       q2 = applyExists (&&) f1 f4 [2]
--       dag0 = makeDAG f5
--       dag1 = makeDAG q1
--       dag2 = makeDAG q2

--   viewDAG dag0
--   viewDAG dag1
--   viewDAG dag2