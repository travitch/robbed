module SimpleFormula ( Formula(..)
                     , parseString
                     , interpretFormula
                     , interpretFormulaDefault
                     ) where

import SimpleFormula.Parser
import SimpleFormula.Types

xor :: Bool -> Bool -> Bool
True `xor` True = False
False `xor` False = False
_ `xor` _ = True

impl :: Bool -> Bool -> Bool
True `impl` True = True
True `impl` False = False
False `impl` True = True
False `impl` False = True

biimpl :: Bool -> Bool -> Bool
True `biimpl` True = True
False `biimpl` False = True
_ `biimpl` _ = False

-- | Interpret the given formula @f@ with the given @assignment@ of
-- boolean values to variables.
--
-- If a variable is not found in the assignment, it assumes the
-- default value.
interpretFormulaDefault :: Bool -> Formula -> [(Int, Bool)] -> Bool
interpretFormulaDefault dflt f assign =
  case genericInterpretFormula (maybe (Just dflt) Just) f assign of
    Nothing -> error "interpretFormulaDefault should not be able to generate Nothing"
    Just b -> b

-- | Interpret the given formula @f@ with the given @assignment@ of boolean
-- values to variables.
--
-- The function will return Nothing if there are free variables after
-- the assignment.
interpretFormula :: Formula -> [(Int, Bool)] -> Maybe Bool
interpretFormula = genericInterpretFormula (maybe Nothing Just)

genericInterpretFormula :: (Maybe Bool -> Maybe Bool) -> Formula ->
                           ([(Int, Bool)] -> Maybe Bool)
genericInterpretFormula lookupWrapper f assignment = translate f
  where
    binOp op f1 f2 = do
      f1' <- translate f1
      f2' <- translate f2
      return (f1' `op` f2')

    translate (Var i) = lookupWrapper $ lookup i assignment
    translate (Not f1) = do
      f' <- translate f1
      return (not f')
    translate (And f1 f2) = binOp (&&) f1 f2
    translate (Xor f1 f2) = binOp xor f1 f2
    translate (Or f1 f2) = binOp (||) f1 f2
    translate (Impl f1 f2) = binOp impl f1 f2
    translate (BiImpl f1 f2) = binOp biimpl f1 f2
