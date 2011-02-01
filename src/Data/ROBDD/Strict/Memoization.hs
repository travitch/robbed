module Data.ROBDD.Strict.Memoization ( emptyBDDState
                                     , BDDContext
                                     , BDDState(..)
                                     , memoNode
                                     , getMemoNode
                                     , memoize
                                     , runBDDContext
                                     , get
                                     , put
                                     ) where

import Control.Monad.State
import Data.Hashable
import qualified Data.HamtMap as M
import Data.ROBDD.Strict.Types

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


-- A helper to memoize BDD nodes
memoNode :: (Eq a, Ord a, Hashable a) => a -> BDD -> BDDContext a ()
memoNode key val = do
  s <- get
  let memoTable = bddMemoTable s
      memoTable' = M.insert key val memoTable

  put s { bddMemoTable = memoTable' }

getMemoNode :: (Eq a, Ord a, Hashable a) => a -> BDDContext a (Maybe BDD)
getMemoNode key = do
  s <- get
  let memoTable = bddMemoTable s

  return $ M.lookup key memoTable

memoize :: (Eq a, Ord a, Hashable a) => a -> State (BDDState a) BDD ->
           BDDContext a BDD
memoize uid act = do
  mem <- getMemoNode uid
  case mem of
    Just node -> return node
    Nothing -> act

runBDDContext :: State s a -> s -> (a, s)
runBDDContext = runState