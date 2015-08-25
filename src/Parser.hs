
module Parser where

import Text.ParserCombinators.Parsec
import System.Environment
import Control.Monad

-- AST types

data Expr = IntLiteral Integer
          | FloatLiteral Float
          | SymbolLiteral String
          | StringLiteral String
          | List [Expr]
          deriving (Show)

-- Parser functions

symbolChars :: String
symbolChars = "!#$%&|*+-/:<=>?@^_~" ++ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

lispsymbol :: Parser Expr
lispsymbol = liftM SymbolLiteral (many1 (oneOf symbolChars))

integer :: Parser Expr
integer = liftM (IntLiteral . Prelude.read) (many1 digit)

float :: Parser Expr
float = do
  whole <- many1 digit
  char '.'
  fraction <- many1 digit
  return (FloatLiteral (Prelude.read $ whole ++ "." ++ fraction))

number :: Parser Expr
number = do
  n <- try float <|> integer
  notFollowedBy (oneOf symbolChars)
  return n

listEnd :: Parser [Expr]
listEnd = return []

listBody :: Parser [Expr]
listBody = do
  car <- expr
  spaces
  cdr <- try listBody <|> listEnd
  return (car:cdr)

list :: Parser Expr
list = do
  whitespace
  char '('
  whitespace
  body <- try listBody <|> listEnd
  whitespace
  char ')'
  return (List body)

expr :: Parser Expr
expr = number
       <|> lispsymbol
       <|> list

whitespace :: Parser ()
whitespace = skipMany space

readAll :: Parser [Expr]
readAll = do
  whitespace
  result <- many $ do
    e <- expr
    whitespace
    return e
  eof
  return result

-- Interface

parseToplevel :: String -> [Expr]
parseToplevel input = case parse readAll "lisp" input of
  Left err -> error $ "No match: " ++ show err
  Right val -> val
