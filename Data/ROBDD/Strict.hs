module Data.ROBDD.Strict ( BDD(..)
                         , mk
                         , apply
                         ) where

import Data.HamtMap (HamtMap)
import qualified Data.HamtMap as M

-- type NodeMap = HamtMap NodeId BDD
type RevMap = HamtMap (Var, NodeId, NodeId) BDD

type NodeId = Int
type Var = Int

-- Node types
data BDD = BDD BDD Var BDD NodeId
         | Zero
         | One

-- Accessible wrapper
data ROBDD = ROBDD RevMap BDD

-- instance Hashable BDD where
--   hash Zero = hash 0
--   hash One = hash 1
--   hash (BDD low v high _) = (hash low) `combine` (hash v) `combine` (hash high)

instance Eq BDD where
  Zero == Zero = True
  One == One = True
  (BDD _ _ _ id1) == (BDD _ _ _ id2) = id1 == id2
  _ == _ = False

-- Lets have IDs start at 2, since Zero and One are logically taken
newIdSource :: [Int]
newIdSource = [2..]

revLookup :: Var -> BDD -> BDD -> RevMap -> Maybe BDD
revLookup v (BDD _ _ _ leftId) (BDD _ _ _ rightId) h =
  M.lookup (v, leftId, rightId) h
revLookup _ _ _ _ = error "Zero and One are not allowed in revLookup"

revInsert :: Var -> BDD -> BDD -> BDD -> RevMap -> RevMap
revInsert v (BDD _ _ _ lowId) (BDD _ _ _ highId) newNode h =
  M.insert (v, lowId, highId) newNode h
revInsert _ _ _ _ _ = error "Zero and One are not allowed in revInsert"

-- | The MK operation.  Re-use an existing BDD node if possible.
-- Otherwise create a new node with the provided NodeId, updating the
-- tables.
mk :: RevMap -> [NodeId] -> Var -> BDD -> BDD ->
      (BDD, RevMap, [NodeId])
mk revMap ids@(thisId:rest) v low high =
  if low == high then (low, revMap, ids) -- Inputs identical, re-use
  else case revLookup v low high revMap of
    Just node -> (node, revMap, ids) -- Return existing node
    -- Make a new node
    Nothing -> (newNode, revMap', rest)
  where newNode = BDD low v high thisId
        revMap' = revInsert v low high newNode revMap


type ApplyCache = HamtMap (NodeId, NodeId) BDD

applyCacheLookup :: BDD -> BDD -> ApplyCache -> Maybe BDD
applyCacheLookup (BDD _ _ _ id1) (BDD _ _ _ id2) ac =
  M.lookup (id1, id2) ac
applyCacheLookup _ _ _ = error "Zero and One are not allowed in applyCacheLookup"

toBool :: BDD -> Maybe Bool
toBool One = Just True
toBool Zero = Just False
toBool _ = Nothing

-- | Construct a new BDD by applying the provided binary operator
-- to the two input BDDs
--
-- Note: the reverse node maps of each input BDD are ignored because
-- we need to build a new one on the fly for the result BDD.
apply :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> ROBDD
apply op (ROBDD _ bdd1) (ROBDD _ bdd2) =
  let (res, rmap, _, _) = appCachedOrBase M.empty M.empty newIdSource bdd1 bdd2
  in ROBDD rmap res
  where appCachedOrBase revMap appCache idSource lhs rhs =
          case applyCacheLookup lhs rhs appCache of
            Just cachedVal -> (cachedVal, revMap, appCache, idSource)
            Nothing -> case maybeApply lhs rhs of
              Just True -> (One, revMap, appCache, idSource)
              Just False -> (Zero, revMap, appCache, idSource)
              Nothing -> appRec revMap appCache idSource lhs rhs
        -- FIXME? Is it the case that we cannot have a terminal compared against
        -- a nonterminal here?
        appRec revMap appCache idSource lhs@(BDD low1 var1 high1 uid1) rhs@(BDD low2 var2 high2 uid2) =
          let ((newNode, revMap', idSrc'), cache') =
                case var1 `compare` var2 of
                  -- Vars are the same
                  EQ -> let (newLowNode, revMap1, cache1, idSrc1) = appCachedOrBase revMap appCache idSource low1 low2
                            (newHighNode, revMap2, cache2, idSrc2) = appCachedOrBase revMap1 cache1 idSrc1 high1 high2
                        in (mk revMap2 idSrc2 var1 newLowNode newHighNode, cache2)
                  -- Var1 is less than var2
                  LT -> let (newLowNode, revMap1, cache1, idSrc1) = appCachedOrBase revMap appCache idSource low1 rhs
                            (newHighNode, revMap2, cache2, idSrc2) = appCachedOrBase revMap1 cache1 idSrc1 high1 rhs
                        in (mk revMap2 idSrc2 var1 newLowNode newHighNode, cache2)
                  -- Var1 is greater than v2
                  GT -> let (newLowNode, revMap1, cache1, idSrc1) = appCachedOrBase revMap appCache idSource lhs low2
                            (newHighNode, revMap2, cache2, idSrc2) = appCachedOrBase revMap1 cache1 idSrc1 lhs high2
                        in (mk revMap2 idSrc2 var2 newLowNode newHighNode, cache2)
              cache'' = M.insert (uid1, uid2) newNode cache'
          in (newNode, revMap', cache'', idSrc')

        maybeApply lhs rhs = do
          b1 <- toBool lhs
          b2 <- toBool rhs
          return $ b1 `op` b2