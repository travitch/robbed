module Data.ROBDD.Strict.Types ( BDD(..)
                               , ROBDD(..)
                               , NodeId
                               , Var
                               , RevMap
                               , Map
                               , bddCmp
                               , highEdge
                               , lowEdge
                               , nodeVar
                               , nodeUID
                               ) where

import Data.GraphViz
import Data.HamtMap (HamtMap)

type Map = HamtMap

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
