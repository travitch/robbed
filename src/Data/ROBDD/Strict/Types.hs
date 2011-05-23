module Data.ROBDD.Strict.Types ( BDD(..)
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
                               ) where

import Data.GraphViz
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
import Data.Graph.Inductive (Gr, mkGraph)

type Map = HashMap

type RevMap = Map (Var, NodeId, NodeId) BDD

type NodeId = Int
type Var = Int

type DAG = Gr BDD Bool

-- Node types FIXME: Add another Int field to each BDD node to act as
-- a hash code.  Assign values to Zero and One, then the hash code for
-- each node is: hash nodeid `combine` leftHash `combine` rightHash
-- This will allow for constant time equality tests between unrelated
-- BDDs.  This is much simpler (though less efficient) than sharing
-- structure between unrelated BDDs.  To do that efficiently, some
-- kind of weak reference is required, otherwise it would leak memory
-- like crazy.
data BDD = BDD BDD Var BDD NodeId
         | Zero
         | One

-- Accessible wrapper
data ROBDD = ROBDD RevMap [Int] BDD

instance Show ROBDD where
  show bdd = prettyPrint' $ graphToDot nonClusteredParams $ makeDAG bdd

instance Eq BDD where
  Zero == Zero = True
  One == One = True
  (BDD _ _ _ id1) == (BDD _ _ _ id2) = id1 == id2
  _ == _ = False

-- ROBDDs are equal as long as their payload BDDs are equal; the
-- metadata does not need to be the same
instance Eq ROBDD where
  (ROBDD _ _ bdd1) == (ROBDD _ _ bdd2) = bdd1 == bdd2

instance Labellable BDD where
  toLabel Zero = toLabel "Zero"
  toLabel One = toLabel "One"
  toLabel (BDD _ v _ _) = toLabel $ show v


-- This is not an Ord instance because the EQ it returns is not the same
-- as the Eq typeclass - it is variable based instead of identity based
bddCmp :: BDD -> BDD -> Ordering
Zero `bddCmp` Zero = EQ
One `bddCmp` One = EQ
Zero `bddCmp` One = GT
One `bddCmp` Zero = LT
(BDD _ _ _ _) `bddCmp` Zero = LT
(BDD _ _ _ _) `bddCmp` One = LT
Zero `bddCmp` (BDD _ _ _ _) = GT
One `bddCmp` (BDD _ _ _ _) = GT
(BDD _ v1 _ _) `bddCmp` (BDD _ v2 _ _) = v1 `compare` v2

varBddCmp :: Var -> BDD -> Ordering
varBddCmp _ Zero = LT
varBddCmp _ One = LT
varBddCmp v (BDD _ b _ _) = v `compare` b

highEdge :: BDD -> BDD
highEdge (BDD _ _ h _) = h
highEdge _ = error "No high edge in Zero or One"

lowEdge :: BDD -> BDD
lowEdge (BDD l _ _ _) = l
lowEdge _ = error "No low edge in Zero or One"

nodeVar :: BDD -> Var
nodeVar (BDD _ v _ _) = v
nodeVar _ = error "No variable for Zero or One"

nodeUID :: BDD -> Int
nodeUID Zero = (-1)
nodeUID One = (-2)
nodeUID (BDD _ _ _ uid) = uid

makeDAG :: ROBDD -> DAG
makeDAG (ROBDD _ _ bdd) = mkGraph nodeList (map unTuple $ M.toList edges)
  where
    nodes :: Map Var BDD
    nodes = collectNodes bdd M.empty
    nodeList :: [ (Var, BDD) ]
    nodeList = M.toList nodes
    collectNodes :: BDD -> Map Var BDD -> Map Var BDD
    collectNodes b@(BDD low v high _) s =
      let s' = collectNodes low s
          s'' = collectNodes high s'
      in M.insert v b s''
    collectNodes Zero s = M.insert (-1) Zero s
    collectNodes One s = M.insert (-2) One s
    edges :: Map (Var, Var) Bool
    edges = collectEdges bdd M.empty
    collectEdges :: BDD -> Map (Var, Var) Bool -> Map (Var, Var) Bool
    collectEdges (BDD low v high _) s =
      let s' = collectEdges low s
          s'' = collectEdges high s'
          s''' = M.insert (v, bddVarNum low) False s''
      in M.insert (v, bddVarNum high) True s'''
    collectEdges _ s = s
    unTuple ((a, b), c) = (a, b, c)

    bddVarNum :: BDD -> Var
    bddVarNum Zero = -1
    bddVarNum One = -2
    bddVarNum (BDD _ v _ _) = v
