module SimpleFormula.Types ( Formula(..) ) where

import Text.Printf

-- | A simple type to represent Boolean formulas including the common
-- operators.
data Formula = And Formula Formula
             | Or Formula Formula
             | Impl Formula Formula
             | BiImpl Formula Formula
             | Xor Formula Formula
             | Not Formula
             | Var Int
             deriving (Eq)

instance Show Formula where
  show = showFormula

precedence :: Formula -> Int
precedence (Var _) = 0
precedence (Not _) = 1
precedence (And _ _) = 2
precedence (Xor _ _) = 3
precedence (Or _ _) = 3
precedence (Impl _ _) = 4
precedence (BiImpl _ _) = 5

precWrap :: Formula -> Formula -> String
precWrap op operand = case precedence op < precedence operand of
  True -> concat ["(", showFormula operand, ")"]
  False -> showFormula operand

showFormula :: Formula -> String
showFormula (Var i) = printf "x[%d]" i
showFormula n@(Not f) =
  printf "!%s" (precWrap n f)
showFormula a@(And f1 f2) =
  printf "%s & %s" (precWrap a f1) (precWrap a f2)
showFormula x@(Xor f1 f2) =
  printf "%s ^ %s" (precWrap x f1) (precWrap x f2)
showFormula o@(Or f1 f2) =
  printf "%s | %s" (precWrap o f1) (precWrap o f2)
showFormula i@(Impl f1 f2) =
  printf "%s -> %s" (precWrap i f1) (precWrap i f2)
showFormula b@(BiImpl f1 f2) =
  printf "%s <-> %s" (precWrap b f1) (precWrap b f2)
