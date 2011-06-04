module Data.ROBDD.Strict ( ROBDD
                         , apply
                         , applyExists
                         , applyForAll
                         , applyUnique
                         , restrict
                         , restrictAll
                         , replace
                         , anySat
                         , satCount
                         , allSat
                         , allSat'
                         , makeVar
                         , makeTrue
                         , makeFalse
                         , and
                         , or
                         , xor
                         , impl
                         , biimpl
                         , nand
                         , nor
                         , neg
                         , exist
                         , forAll
                         , unique
                         ) where

import Prelude hiding (and, or)
import Data.Foldable (toList)
import Data.List (sort)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable
import qualified Data.Sequence as Seq
import Data.Sequence ((><))

import Data.ROBDD.BooleanFunctions
import Data.ROBDD.Strict.Types

type BinBoolFunc = Bool -> Bool -> Bool

-- | Make the BDD representing True (One)
makeTrue :: ROBDD
makeTrue = ROBDD M.empty [0..] One

-- | Make the BDD representing False (Zero)
makeFalse :: ROBDD
makeFalse = ROBDD M.empty [0..] Zero


-- | Make a single BDD variable with the given number.  The number is
-- used to identify the variable in other functions (like
-- quantification).  The number must be non-negative; negative numbers
-- will cause an error to be raised.
makeVar :: Var -> ROBDD
makeVar v
  | v >= 0 = ROBDD M.empty [0..] bdd
  | otherwise = error "Variable numbers must be >= 0"
  where
    bdd = BDD Zero v One 0 (hashNode v Zero One)


and :: ROBDD -> ROBDD -> ROBDD
and = apply (&&)

or :: ROBDD -> ROBDD -> ROBDD
or = apply (||)

xor :: ROBDD -> ROBDD -> ROBDD
xor = apply boolXor

impl :: ROBDD -> ROBDD -> ROBDD
impl = apply boolImpl

biimpl :: ROBDD -> ROBDD -> ROBDD
biimpl = apply boolBiimp

nand :: ROBDD -> ROBDD -> ROBDD
nand = apply boolNotAnd

nor :: ROBDD -> ROBDD -> ROBDD
nor = apply boolNotOr

-- | Existentially quantify a single variable from a BDD
exist :: ROBDD -> Var -> ROBDD
exist bdd var = or (restrict bdd var True) (restrict bdd var False)

-- | Uniquely quantify a single variable from a BDD.
unique :: ROBDD -> Var -> ROBDD
unique bdd var = xor (restrict bdd var True) (restrict bdd var False)

-- | forAll quantify the given variable
forAll :: ROBDD -> Var -> ROBDD
forAll bdd var = and (restrict bdd var True) (restrict bdd var False)

-- | Construct a new BDD by applying the provided binary operator
-- to the two input BDDs
--
-- Note: the reverse node maps of each input BDD are ignored because
-- we need to build a new one on the fly for the result BDD.
apply :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> ROBDD
apply op (ROBDD _ _ bdd1) (ROBDD _ _ bdd2) =
  let (bdd, s) = runBDDContext (applyInner op stdCtxt bdd1 bdd2) emptyBDDState
      -- FIXME: Remove unused bindings in the revmap to allow the
      -- runtime to GC unused nodes
  in ROBDD (bddRevMap s) (bddIdSource s) bdd


-- This is the main implementation of apply, but also re-used for the
-- combined apply/quantify operations.
applyInner :: BinBoolFunc -> EvaluationContext -> BDD -> BDD ->
              BDDContext (Int, NodeId, NodeId) BDD BDD
applyInner op ctxt bdd1 bdd2 = appBase bdd1 bdd2
  where
    appBase :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD BDD
    appBase lhs rhs = memoize (ctxt, nodeUID lhs, nodeUID rhs) $ do
      case maybeApply op lhs rhs of
        Just True -> return One
        Just False -> return Zero
        Nothing -> appRec lhs rhs

    appRec :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD BDD
    appRec lhs rhs = do
      (v, l', h') <- genApplySubproblems appBase lhs rhs
      mk v l' h'

maybeApply :: (Bool -> Bool -> Bool) -> BDD -> BDD -> Maybe Bool
maybeApply op lhs rhs = do
  b1 <- toBool lhs
  b2 <- toBool rhs
  return $ b1 `op` b2

toBool :: BDD -> Maybe Bool
toBool One = Just True
toBool Zero = Just False
toBool _ = Nothing

-- This is the core of apply that determines the subproblems to evaluate
-- at this step.  The appBase argument is the action that should be
-- called recursively for each sub problem.
genApplySubproblems :: (Monad m) => (BDD -> BDD -> m BDD) -> BDD -> BDD ->
                       m (Var, BDD, BDD)
genApplySubproblems appBase lhs rhs = case lhs `bddCmp` rhs of
  -- Vars are the same, so use high and low of both lhs and rhs as the
  -- sub-problem
  EQ -> do
    newLowNode <- appBase (lowEdge lhs) (lowEdge rhs)
    newHighNode <- appBase (highEdge lhs) (highEdge rhs)
    return (nodeVar lhs, newLowNode, newHighNode)
  -- Var1 is less than var2, so only take the low/high edges of the
  -- lhs (pass the RHS through unchanged)
  LT -> do
    newLowNode <- appBase (lowEdge lhs) rhs
    newHighNode <- appBase (highEdge lhs) rhs
    return (nodeVar lhs, newLowNode, newHighNode)

    -- Var1 is greater than v2
  GT -> do
    newLowNode <- appBase lhs (lowEdge rhs)
    newHighNode <- appBase lhs (highEdge rhs)
    return (nodeVar rhs, newLowNode, newHighNode)


-- This is the main implementation of the combined apply/quantify
-- operators.  They are really all the same except for the
-- quantification operator.
genericApply :: BinBoolFunc -> BinBoolFunc ->
                ROBDD -> ROBDD -> [Var] -> ROBDD
genericApply quantifier op (ROBDD _ _ bdd1) (ROBDD _ _ bdd2) evars =
  let (bdd, s) = runBDDContext (appBase bdd1 bdd2) emptyBDDState
  in ROBDD (bddRevMap s) (bddIdSource s) bdd
  where
    varSet = S.fromList evars
    appBase :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD BDD
    appBase lhs rhs = memoize (stdCtxt, nodeUID lhs, nodeUID rhs) $ do
      case maybeApply op lhs rhs of
        Just True -> return One
        Just False -> return Zero
        Nothing -> appRec lhs rhs
    appRec :: BDD -> BDD -> BDDContext (EvaluationContext, NodeId, NodeId) BDD BDD
    appRec lhs rhs = do
      (v', l', h') <- genApplySubproblems appBase lhs rhs
      case v' `S.member` varSet of
        False -> mk v' l' h'
        -- ^ Standard case - we are not projecting out this variable
        -- so just let mk handle creating a new node if necessary
        True -> applyInner quantifier innerCtxt l' h'
        -- ^ If this variable is to be quantified out, this magic is
        -- due to McMillan 92; we quantify it out while we are
        -- building the tree via a call to or.  This re-uses the
        -- current BDD context and so does not use the top-level
        -- or, but the underlying machinery
        -- See http://www.kenmcmil.com/pubs/thesis.pdf
        --
        -- The quantification returns the formula that would
        -- result if a variable V is declared to be forall,
        -- unique, or exists; it does this by invoking either and,
        -- xor, or or on the sub-problems for any step where V is
        -- the leading variable.

-- | A variant of apply that existentially quantifies out the provided
-- list of variables on the fly during the bottom-up construction of
-- the result.  This is much more efficient than performing the
-- quantification after the apply.
applyExists :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyExists = genericApply (||)
applyUnique :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyUnique = genericApply boolXor
applyForAll :: (Bool -> Bool -> Bool) -> ROBDD -> ROBDD -> [Var] -> ROBDD
applyForAll = genericApply (&&)

-- | Fix the value of a variable in the formula
restrict :: ROBDD -> Var -> Bool -> ROBDD
restrict bdd@(ROBDD _ _ Zero) _ _ = bdd
restrict bdd@(ROBDD _ _ One) _ _ = bdd
restrict (ROBDD revMap idSrc bdd) v b =
  let (r,s) = runBDDContext (restrict' bdd) emptyBDDState { bddIdSource = idSrc
                                                          , bddRevMap = revMap
                                                          }
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where
    restrict' Zero = return Zero
    restrict' One = return One
    restrict' o@(BDD low var high uid _) = memoize uid $ do
      case var `compare` v of
        GT -> return o
        LT -> do
          low' <- restrict' low
          high' <- restrict' high
          mk var low' high'
        EQ -> case b of
          True -> restrict' high
          False -> restrict' low

-- | restrict over a list of variable/value pairs.  This should be
-- more efficient than repeated calls to restrict.
restrictAll :: ROBDD -> [(Var, Bool)] -> ROBDD
restrictAll bdd@(ROBDD _ _ Zero) _ = bdd
restrictAll bdd@(ROBDD _ _ One) _ = bdd
restrictAll (ROBDD revMap idSrc bdd) vals =
  let (r, s) = runBDDContext (restrict' bdd) emptyBDDState { bddIdSource = idSrc
                                                           , bddRevMap = revMap
                                                           }
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where
    valMap = M.fromList vals
    restrict' Zero = return Zero
    restrict' One = return One
    restrict' (BDD low var high uid _) = memoize uid $ do
      case var `M.lookup` valMap of
        Just b -> case b of
          True -> restrict' high
          False -> restrict' low
        Nothing -> do
          low' <- restrict' low
          high' <- restrict' high
          mk var low' high'

-- | Rename BDD variables according to the @mapping@ provided as an
-- alist.  This can be a potentially very expensive operation.
replace :: ROBDD -> [(Var, Var)] -> ROBDD
replace (ROBDD revMap idSrc bdd) mapping =
  let (r, s) = runBDDContext (replace' bdd) emptyBDDState { bddIdSource = idSrc
                                                          , bddRevMap = revMap
                                                          }
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where
    m = M.fromList mapping
    replace' Zero = return Zero
    replace' One = return One
    replace' (BDD low var high uid _) = memoize uid $ do
      low' <- replace' low
      high' <- replace' high
      let level = M.lookupDefault var var m
          -- ^ The remapped level - default is the current level
      fixSubgraph level uid low' high'
      -- innerState <- getBDDState
      -- let (r, s') = runBDDContext fixup emptyBDDState { bddIdSource = bddIdSource innerState
      --                                                 , bddRevMap = bddRevMap innerState
      --                                                 }
      -- putBDDState emptyBDDState { bddIdSource = bddIdSource s'
      --                           , bddRevMap = bddRevMap s'
      --                           }
      -- return r
    -- FIXME: I don't know that uid is the right thing to memoize on
    -- here...
    fixSubgraph level uid low high
      | level `varBddCmp` low == LT && level `varBddCmp` high == LT =
        {-memoize uid-} (mk level low high)
      | level `varBddCmp` low == EQ || level `varBddCmp` high == EQ =
          error ("Bad replace at " ++ show level ++ ": " ++ show mapping)
      | otherwise = {-memoize uid $-} do
        case low `bddCmp` high of
          EQ -> do
            l <- fixSubgraph level (nodeUID low) (lowEdge low) (lowEdge high)
            r <- fixSubgraph level (nodeUID high) (highEdge low) (highEdge high)
            mk (nodeVar low) l r
          LT -> do
            l <- fixSubgraph level (nodeUID low) (lowEdge low) high
            r <- fixSubgraph level (nodeUID high) (highEdge low) high
            mk (nodeVar low) l r
          GT -> do
            l <- fixSubgraph level (nodeUID low) low (lowEdge high)
            r <- fixSubgraph level (nodeUID high) low (highEdge high)
            mk (nodeVar high) l r


-- | negate the given BDD.  This implementation is somewhat more
-- efficient than the naiive translation to BDD -> False.
-- Unfortunately, it isn't as much of an improvement as it could be
-- via destructive updates. FIXME: Implement constant-time negation
-- either via negation arcs or just a flag on the ROBDD structure
neg :: ROBDD -> ROBDD
neg (ROBDD _ _ bdd) =
  -- Everything gets re-allocated so don't bother trying to re-use the
  -- revmap or idsource
  let (r, s) = runBDDContext (negate' bdd) emptyBDDState
  in ROBDD (bddRevMap s) (bddIdSource s) r
  where
    negate' Zero = return One
    negate' One = return Zero
    negate' (BDD low var high uid _) = memoize uid $ do
      low' <- negate' low
      high' <- negate' high
      mk var low' high'

-- | Count the number of satisfying assignments to the BDD.
-- O(|v|)
satCount :: ROBDD -> Int
satCount (ROBDD revMap _ bdd) =
  fst $ runBDDContext (count' bdd) emptyBDDState
  where
    varCount = maximum $ map (\(v,_,_) -> v) $ M.keys revMap
    safeNodeVar n = case n of
      Zero -> varCount + 1
      One -> varCount + 1
      _ -> nodeVar n
    count' Zero = return 0
    count' One = return 1
    count' (BDD low v high uid _) = memoize uid $ do
      l <- count' low
      r <- count' high
      let lc = 2 ^ (safeNodeVar low - v - 1)
          hc = 2 ^ (safeNodeVar high - v - 1)
      return (lc*l + hc*r)

-- | Return an arbitrary assignment of values to variables to make the
-- formula true
anySat :: ROBDD -> Maybe [(Var, Bool)]
anySat (ROBDD _ _ Zero) = Nothing
anySat (ROBDD _ _ One) = Just []
anySat (ROBDD _ _ bdd) = Just $ sat' bdd []
  where
    sat' One acc = acc
    sat' Zero _ = error "anySat should not hit Zero"
    sat' (BDD low v high _ _) acc =
      case low of
        Zero -> (v, True) : sat' high acc
        _ -> (v, False) : sat' low acc

-- | Extract all satisfying variable assignments to the BDD as a list of
-- association lists.  O(2^n)
allSat :: ROBDD -> [[(Var, Bool)]]
allSat (ROBDD _ _ Zero) = []
allSat (ROBDD _ _ One) = [[]]
allSat (ROBDD _ _ bdd) =
  toList $ fst $ runBDDContext (sat' bdd) emptyBDDState
  where
    sat' Zero = return Seq.empty
    sat' One = return $ Seq.singleton []
    sat' (BDD low v high uid _) = memoize uid $ do
      l <- sat' low
      r <- sat' high
      let l' = fmap ((v,False):) l
          r' = fmap ((v,True):) r
      return (l' >< r')

-- | Extract all satisfying solutions to the BDD, but also ensuring
-- that assignments are provided for all of the @activeVars@.  A
-- normal 'allSat' only provides assignments for variables appearing
-- in the BDD (i.e. the variables whose values are not arbitrary).
-- Some applications also need assignments for the arbitrary
-- variables, but the allSat algorithm cannot know which variables to
-- include without the activeVars parameter.
allSat' :: ROBDD -> [Int] -> [[(Var, Bool)]]
allSat' (ROBDD _ _ Zero) _ = []
allSat' (ROBDD _ _ bdd) activeVars =
  toList $ fst $ runBDDContext (sat' bdd vars) emptyBDDState
  where
    vars = sort activeVars
    sat' Zero _ = return Seq.empty
    sat' One _ = return $ Seq.singleton []
    sat' (BDD low v high uid _) vs = memoize uid $ do
      let (lLocalVars, lLowerVars) = arbitraryVars vs v low
          (rLocalVars, rLowerVars) = arbitraryVars vs v high
      -- ^ The localVars are those that can be arbitrary on their
      -- respective branches.
      l <- sat' low lLowerVars
      r <- sat' high rLowerVars
      -- ^ Computed the satisfying assignments for child trees - add in
      -- corrections to each branch before adding the assignment for
      -- this variable
      let l' = addArbitrary lLocalVars l
          r' = addArbitrary rLocalVars r
          l'' = fmap ((v, False):) l'
          r'' = fmap ((v, True):) r'
      return (l'' >< r'')
    arbitraryVars vs v Zero = (filter (/=v) vs, [])
    arbitraryVars vs v One = (filter (/=v) vs, [])
    arbitraryVars vs vLocal (BDD _ vNext _ _ _) =
      let (local, lower) = span (<vNext) vs
      in (filter (/=vLocal) local, lower)
    addArbitrary [] subsols = subsols
    addArbitrary (v:vs) subsols =
      let s' = addArbitrary vs subsols
          l = fmap ((v, False):) s'
          r = fmap ((v, True):) s'
          -- ^ This value can be arbitrary, so add solutions for both
          -- possible truth assignments.
      in l >< r

-- TODO: compose

-- The MK operation.  Re-use an existing BDD node if possible.
-- Otherwise create a new node with the provided NodeId, updating the
-- tables.  This is not exported and just used internally.  It lives
-- in the BDDContext monad, which holds the result cache (revLookup
-- map)
mk :: Var -> BDD -> BDD -> BDDContext a BDD BDD
mk v low high = do
  s <- getBDDState

  let revMap = bddRevMap s

  if low == high
    then return low -- Inputs identical, re-use
    else case revLookup v low high revMap of
      -- Return existing node
      Just node -> return node
      -- Make a new node
      Nothing -> revInsert v low high

-- Helpers for mk
revLookup :: Var -> BDD -> BDD -> RevMap -> (Maybe BDD)
revLookup v leftTarget rightTarget revMap = do
  M.lookup (v, nodeUID leftTarget, nodeUID rightTarget) revMap

hashNode :: Var -> BDD -> BDD -> Int
hashNode v low high =
  v `combine` nodeHash low `combine` nodeHash high

-- Create a new node for v with the given high and low edges.
-- Insert it into the revMap and return it.
revInsert :: Var -> BDD -> BDD -> BDDContext a BDD BDD
revInsert v lowTarget highTarget = do
  s <- getBDDState
  let revMap = bddRevMap s
      (nodeId:rest) = bddIdSource s
      revMap' = M.insert (v, nodeUID lowTarget, nodeUID highTarget) newNode revMap
      h = hashNode v lowTarget highTarget
      newNode = BDD lowTarget v highTarget nodeId h
  putBDDState s { bddRevMap = revMap'
                , bddIdSource = rest
                }

  return newNode



-- Evaluation contexts are tags used in the memoization table to
-- differentiate memo entries from different contexts.  This is
-- important for the genericApply function, which has a set of
-- memoized values for its arguments.  It recursively calls the normal
-- apply driver, which must maintain separate memoized values
-- (otherwise you get incorrect results).
type EvaluationContext = Int

stdCtxt :: EvaluationContext
stdCtxt = 1

innerCtxt :: EvaluationContext
innerCtxt = 2

