module Data.ROBDD.Strict.Visualization ( DAG
                                       , makeDAG
                                       , viewDAG
                                       ) where

import qualified Data.HamtMap as M
import Data.Graph.Inductive (Gr, mkGraph)
import Data.GraphViz

import Data.ROBDD.Strict
import Data.ROBDD.Strict.Types

type DAG = Gr BDD Bool

makeDAG :: ROBDD -> DAG
makeDAG (ROBDD _ _ bdd) = mkGraph nodeList (map unTuple $ M.toList edges)
  where nodes :: Map Var BDD
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


viewDAG :: DAG -> IO ()
viewDAG dag = do
  let dg = graphToDot nonClusteredParams dag
  s <- prettyPrint dg
  putStrLn s
  preview dag
