{-# LANGUAGE NoMonomorphismRestriction #-}
module Data.ROBDD.Strict.Memoization (
                                     ) where

import Control.Monad.State
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M
-- import Data.ROBDD.Strict.Types

type Map = HashMap

