module SimpleFormula.Parser ( parseString ) where

import Control.Applicative hiding ((<|>), many)
import Text.Parsec
import Text.Parsec.Expr

import SimpleFormula.Types

type FormulaParser = Parsec [Char] ()

parseString :: String -> Either ParseError Formula
parseString = parse parseFormula "<input>"

parseFormula :: FormulaParser Formula
parseFormula = buildExpressionParser table term <?> "Formula"
  where
    table = [ [ prefix "!" Not ]
            , [ binary "&" And AssocLeft, binary "AND" And AssocLeft ]
            , [ binary "^" Xor AssocLeft, binary "XOR" Xor AssocLeft
              , binary "|" Or AssocLeft, binary "OR" Or AssocLeft ]
            , [ binary "->" Impl AssocLeft, binary "IMPL" Impl AssocLeft ]
            , [ binary "<->" BiImpl AssocLeft, binary "BIIMPL" BiImpl AssocLeft ]
            ]
    binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
    prefix  name fun       = Prefix (do{ reservedOp name; return fun })


parens :: FormulaParser a -> FormulaParser a
parens p = (spaces >> char '(' >> spaces) *> p <* (spaces >> char ')' >> spaces)

reservedOp :: String -> FormulaParser ()
reservedOp s = spaces >> string s >> spaces

natural :: FormulaParser Int
natural = read <$> many1 digit

term :: FormulaParser Formula
term = parens parseFormula <|> parseVariable <?> "atom"

parseVariable :: FormulaParser Formula
parseVariable = Var <$> ((spaces >> string "x[") *> natural <* (string "]" >> spaces))
