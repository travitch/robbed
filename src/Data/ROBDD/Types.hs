{-# LANGUAGE NoMonomorphismRestriction, RankNTypes #-}
module Data.ROBDD.Types ( BDD(..)
                        , ROBDD(..)
                        , NodeId
                        , Var
                        , RevMap
                        , Map
                        , DAG
                        , makeDAG
                        , bddCmp
                        , varBddCmp
                        , highEdge
                        , lowEdge
                        , nodeVar
                        , nodeUID
                        , nodeHash
                        , emptyBDDState
                        , BDDContext
                        , BDDState(..)
                        , memoize
                        , runBDDContext
                        , getBDDState
                        , putBDDState
                        ) where

import Control.Monad.State
import Data.GraphViz
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Data.Hashable
import Data.Graph.Inductive (Gr, mkGraph)

type Map = HashMap

type RevMap = Map (Var, NodeId, NodeId) BDD

type NodeId = Int
type Var = Int

-- | A type for a graph representation of a BDD.  This is used for
-- visualization
type DAG = Gr BDD Bool

-- | This is actually an internal type to represent BDD structure.
-- Additional bookkeeping information is required to really manipulate
-- a BDD, so 'ROBDD' is the externally-visible version.
--
-- The two BDD fields are the low and high children, respectively.
-- The Var field is the name of the BDD variable at this node.
-- The NodeId is a unique identifier that is used to uniquely identify
-- nodes in the node cache (see 'RevMap').
--
-- The last Int field is a structural hash.  Normal BDD packages cache
-- *all* nodes that are ever constructed, so comparisons between
-- unrelated BDDs are still trivial since they all use the same cache.
-- This package is different, in part to make garbage collection
-- easier.  Each separate BDD maintains its own node cache to preserve
-- the canonicity property, but unrelated BDDs will not share nodes.
-- The structural hash allows for fast inequality comparisons between
-- unrelated BDDs.  Equality still requires a full traversal of both
-- BDDs since there could be hash collisions
data BDD = BDD BDD !Var BDD !NodeId !Int
         | Zero
         | One

instance Show BDD where
  show Zero = "Zero"
  show One = "One"
  show (BDD _ v _ _ _) = show v

-- | This is the public wrapper around BDDs.  It maintains some
-- metadata required to manipulate a BDD correctly.
data ROBDD = ROBDD RevMap [Int] BDD

instance Show ROBDD where
  show bdd = prettyPrint' $ graphToDot nonClusteredParams $ makeDAG bdd

instance Eq BDD where
  Zero == Zero = True
  One == One = True
  b1@(BDD _ _ _ _ h1) == b2@(BDD _ _ _ _ h2) = case h1 == h2 of
    False -> False
    True -> b1 `bddEq` b2
  _ == _ = False

-- ROBDDs are equal as long as their payload BDDs are equal; the
-- metadata does not need to be the same
instance Eq ROBDD where
  (ROBDD _ _ bdd1) == (ROBDD _ _ bdd2) = bdd1 == bdd2

instance Labellable BDD where
  toLabel Zero = toLabel "Zero"
  toLabel One = toLabel "One"
  toLabel (BDD _ v _ _ _) = toLabel $ show v


-- This is not an Ord instance because the EQ it returns is not the same
-- as the Eq typeclass - it is variable based instead of identity based
bddCmp :: BDD -> BDD -> Ordering
Zero `bddCmp` Zero = EQ
One `bddCmp` One = EQ
Zero `bddCmp` One = GT
One `bddCmp` Zero = LT
(BDD _ _ _ _ _) `bddCmp` Zero = LT
(BDD _ _ _ _ _) `bddCmp` One = LT
Zero `bddCmp` (BDD _ _ _ _ _) = GT
One `bddCmp` (BDD _ _ _ _ _) = GT
(BDD _ v1 _ _ _) `bddCmp` (BDD _ v2 _ _ _) = v1 `compare` v2

varBddCmp :: Var -> BDD -> Ordering
varBddCmp _ Zero = LT
varBddCmp _ One = LT
varBddCmp v (BDD _ b _ _ _) = v `compare` b

highEdge :: BDD -> BDD
highEdge (BDD _ _ h _ _) = h
highEdge _ = error "No high edge in Zero or One"

lowEdge :: BDD -> BDD
lowEdge (BDD l _ _ _ _) = l
lowEdge _ = error "No low edge in Zero or One"

nodeVar :: BDD -> Var
nodeVar (BDD _ v _ _ _) = v
nodeVar _ = error "No variable for Zero or One"

nodeUID :: BDD -> Int
nodeUID Zero = (-1)
nodeUID One = (-2)
nodeUID (BDD _ _ _ uid _) = uid

nodeHash :: BDD -> Int
nodeHash Zero = 678
nodeHash One = 345
nodeHash (BDD _ _ _ _ h) = h

-- | Convert a BDD into a graph representation appropriate for
-- visualization.  This should be in the visualization module, but it
-- is also used for the BDD 'Show' instance, so it needs to be here.
makeDAG :: ROBDD -> DAG
makeDAG (ROBDD _ _ bdd) = mkGraph nodeList (map unTuple $ M.toList edges)
  where
    nodes :: Map Var BDD
    nodes = collectNodes bdd M.empty
    nodeList :: [ (NodeId, BDD) ]
    nodeList = M.toList nodes
    collectNodes :: BDD -> Map NodeId BDD -> Map NodeId BDD
    collectNodes b@(BDD low _ high uid _) s =
      let s' = collectNodes low s
          s'' = collectNodes high s'
      in M.insert uid b s''
    collectNodes Zero s = M.insert (-1) Zero s
    collectNodes One s = M.insert (-2) One s
    edges :: Map (Var, Var) Bool
    edges = collectEdges bdd M.empty
    collectEdges :: BDD -> Map (NodeId, NodeId) Bool -> Map (NodeId, NodeId) Bool
    collectEdges (BDD low _ high uid _) s =
      let s' = collectEdges low s
          s'' = collectEdges high s'
          s''' = M.insert (uid, bddNodeId low) False s''
      in M.insert (uid, bddNodeId high) True s'''
    collectEdges _ s = s
    unTuple ((a, b), c) = (a, b, c)

    bddNodeId :: BDD -> NodeId
    bddNodeId Zero = -1
    bddNodeId One = -2
    bddNodeId (BDD _ _ _ uid _) = uid

-- | This is the equality test for BDDs.  Inequality is testable in
-- constant time under the current representation, but equality
-- requires this full structural check.  The traversal is memoized
-- and should be reasonably efficient.
bddEq :: BDD -> BDD -> Bool
bddEq b1 b2 =
  fst $ runBDDContext (bddEq' b1 b2) emptyBDDState
  where
    bddEq' Zero Zero = return True
    bddEq' One One = return True
    bddEq' (BDD low1 var1 high1 uid1 h1) (BDD low2 var2 high2 uid2 h2) =
      memoize (uid1, uid2) $ do
        case h1 == h2 && var1 == var2 of
          False -> return False
          -- ^ If the hashes at any level are not equal, we can exit
          -- early.
          True -> do
            l <- bddEq' low1 low2
            r <- bddEq' high1 high2
            return (l && r)
    bddEq' _ _ = return False

-- Types used internally; these are for a State monad that tracks memo
-- tables and revmap updates.
data BDDState a b = BDDState { bddRevMap :: RevMap
                             , bddIdSource :: [Int]
                             , bddMemoTable :: Map a b
                             }

-- Start IDs at 2, since Zero and One are conceptually taken
emptyBDDState :: (Eq a, Hashable a) => BDDState a b
emptyBDDState = BDDState { bddRevMap = M.empty
                         , bddIdSource = [0..]
                         , bddMemoTable = M.empty
                         }

type BDDContext a b c = State (BDDState a b) c


-- A helper to memoize BDD nodes
memoNode :: (Eq a, Ord a, Hashable a) => a -> b -> BDDContext a b ()
memoNode key val = do
  s <- get
  let memoTable = bddMemoTable s
      memoTable' = M.insert key val memoTable

  put s { bddMemoTable = memoTable' }

getMemoNode :: (Eq a, Ord a, Hashable a) => a -> BDDContext a b (Maybe b)
getMemoNode key = do
  s <- get
  let memoTable = bddMemoTable s

  return $ M.lookup key memoTable

memoize :: (Eq a, Ord a, Hashable a) => a -> State (BDDState a b) b ->
            BDDContext a b b
memoize uid act = do
  mem <- getMemoNode uid
  case mem of
    Just node -> return node
    Nothing -> do
      v <- act
      memoNode uid v
      return v

runBDDContext :: State s a -> s -> (a, s)
runBDDContext = runState

getBDDState = get

putBDDState = put
