module Data.ROBDD.Strict ( BDD(..)
                         , mk
                         , apply
                         ) where

import Control.Monad.State
import Data.HamtMap (HamtMap)
import qualified Data.HamtMap as M
import Data.Hashable

type Map = HamtMap

-- type NodeMap = HamtMap NodeId BDD
type RevMap = Map (Var, NodeId, NodeId) BDD

type NodeId = Int
type Var = Int

-- Node types
data BDD = BDD BDD Var BDD NodeId
         | Zero
         | One

-- Accessible wrapper
data ROBDD = ROBDD RevMap [Int] BDD

instance Eq BDD where
  Zero == Zero = True
  One == One = True
  (BDD _ _ _ id1) == (BDD _ _ _ id2) = id1 == id2
  _ == _ = False

data BDDState a = BDDState { bddRevMap :: RevMap
                           , bddIdSource :: [Int]
                           , bddMemoTable :: Map a BDD
                           }
type BDDContext a b = State (BDDState a) b

revLookup :: Var -> BDD -> BDD -> RevMap -> (Maybe BDD)
revLookup v (BDD _ _ _ leftId) (BDD _ _ _ rightId) revMap = do
  M.lookup (v, leftId, rightId) revMap
revLookup _ _ _ _ = error "Zero and One can never be in the RevMap"

-- Create a new node for v with the given high and low edges.
-- Insert it into the revMap and return it.
revInsert :: Var -> BDD -> BDD -> BDDContext a BDD
revInsert v b1@(BDD _ _ _ lowId) b2@(BDD _ _ _ highId) = do
  s <- get
  let revMap = bddRevMap s
      (nodeId:rest) = bddIdSource s
      revMap' = M.insert (v, lowId, highId) newNode revMap
      newNode = BDD b1 v b2 nodeId
  put $ s { bddRevMap = revMap'
          , bddIdSource = rest }

  return newNode

revInsert _ _ _ = error "Zero and one cannot be RevMap keys"

-- Start IDs at 2, since Zero and One are conceptually taken
emptyBDDState :: (Eq a, Hashable a) => BDDState a
emptyBDDState = BDDState { bddRevMap = M.empty
                         , bddIdSource = [2..]
                         , bddMemoTable = M.empty
                         }

-- | The MK operation.  Re-use an existing BDD node if possible.
-- Otherwise create a new node with the provided NodeId, updating the
-- tables.
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

-- | Construct a new BDD by applying the provided binary operator
-- to the two input BDDs
--
-- Note: the reverse node maps of each input BDD are ignored because
-- we need to build a new one on the fly for the result BDD.
apply :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> ROBDD
apply op (ROBDD _ _ bdd1) (ROBDD _ _ bdd2) =
  let (bdd, s) = runState (appCachedOrBase bdd1 bdd2) emptyBDDState
  in ROBDD (bddRevMap s) (bddIdSource s) bdd
  where appCachedOrBase :: BDD -> BDD -> BDDContext (NodeId, NodeId) BDD
        appCachedOrBase lhs@(BDD _ _ _ id1) rhs@(BDD _ _ _ id2) = do
          memNode <- getMemoNode (id1, id2)

          case memNode of
            Just cachedVal -> return cachedVal
            Nothing -> case maybeApply lhs rhs of
              Just True -> return One
              Just False -> return Zero
              Nothing -> appRec lhs rhs
        -- If we don't match both as BDDs, it couldn't have been cached.
        -- Again, is this actually true?
        appCachedOrBase lhs rhs = do
          case maybeApply lhs rhs of
            Just True -> return One
            Just False -> return Zero
            Nothing -> appRec lhs rhs
        -- FIXME? Is it the case that we cannot have a terminal compared against
        -- a nonterminal here?
        appRec :: BDD -> BDD -> BDDContext (NodeId, NodeId) BDD
        appRec lhs@(BDD low1 var1 high1 uid1) rhs@(BDD low2 var2 high2 uid2) = do
          newNode <- case var1 `compare` var2 of
                  -- Vars are the same
                  EQ -> do
                    newLowNode <- appCachedOrBase low1 low2
                    newHighNode <- appCachedOrBase high1 high2
                    mk var1 newLowNode newHighNode
                  -- Var1 is less than var2
                  LT -> do
                    newLowNode <- appCachedOrBase low1 rhs
                    newHighNode <- appCachedOrBase high1 rhs
                    mk var1 newLowNode newHighNode
                  -- Var1 is greater than v2
                  GT -> do
                    newLowNode <- appCachedOrBase lhs low2
                    newHighNode <- appCachedOrBase lhs high2
                    mk var2 newLowNode newHighNode
          memoNode (uid1, uid2) newNode
          return newNode

        maybeApply :: BDD -> BDD -> Maybe Bool
        maybeApply lhs rhs = do
          b1 <- toBool lhs
          b2 <- toBool rhs
          return $ b1 `op` b2

        toBool :: BDD -> Maybe Bool
        toBool One = Just True
        toBool Zero = Just False
        toBool _ = Nothing
