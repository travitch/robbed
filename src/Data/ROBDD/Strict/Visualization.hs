module Data.ROBDD.Strict.Visualization ( viewDAG, makeDAG ) where

import Data.GraphViz
import Data.ROBDD.Strict.Types

viewDAG :: DAG -> IO ()
viewDAG dag = do
  let dg = graphToDot nonClusteredParams dag
  s <- prettyPrint dg
  putStrLn s
  preview dag
