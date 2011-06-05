module Data.ROBDD.Strict.Visualization ( viewDAG, makeDAG ) where

import Data.GraphViz
import Data.ROBDD.Strict.Types

viewDAG :: DAG -> IO ()
viewDAG dag = do
  let params = nonClusteredParams { fmtNode = \(_,l) -> [toLabel l]
                                  , fmtEdge = \(_,_,l) -> [toLabel l]
                                  }
      dg = graphToDot params dag
  s <- prettyPrint dg
  putStrLn s
  _ <- runGraphvizCanvas' dg Gtk
  return ()
