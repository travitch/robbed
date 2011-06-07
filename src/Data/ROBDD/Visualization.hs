module Data.ROBDD.Visualization ( viewBDD ) where

import Data.GraphViz
import Data.ROBDD.Types

-- | Visualize a BDD using GraphViz.  This function pops up a window
-- with the rendered DAG.
viewBDD :: ROBDD -> IO ()
viewBDD bdd = do
  let dag = makeDAG bdd
      params = nonClusteredParams { fmtNode = \(_,l) -> [toLabel l]
                                  , fmtEdge = \(_,_,l) -> [toLabel l]
                                  }
      dg = graphToDot params dag
  s <- prettyPrint dg
  putStrLn s
  _ <- runGraphvizCanvas' dg Gtk
  return ()
