
module Parser where

import Text.ParserCombinators.Parsec
import System.Environment
import Control.Monad
import Data.Maybe

-- AST types

data SExpr = IntLiteral Integer
           | FloatLiteral Float
           | SymbolLiteral String
           | StringLiteral String
           | List [SExpr]
             deriving (Show)

data TDecl = Ptr TDecl
           | Const TDecl
           | Type Term
             deriving (Show)

data Term = TName          { tsrepr :: String }
          | TIntLiteral    { tirepr :: Integer }
          | TFloatLiteral  { tfrepr :: Float }
          | TStringLiteral { tsrepr :: String }
          | TListLiteral   { elems :: [Term] }
          | TFuncall       { tfun :: Term, targs :: [Term] }
          | TDef           { tname :: Term, tdecl :: TDecl, tvalue :: Maybe Term }
          | TLambda        { ttype :: Term, tbindings :: [TDecl], tbody :: [Term] }
          | TStruct        { tname :: Term, tfields :: [Term] }
          | TMacro         { tname :: Term, tbindings :: [TDecl], tbody :: [Term] }
          | TTemplate      { tname :: Term, tbindings :: [TDecl], tbody :: [Term] }
            deriving (Show)

-- Parser functions

symbolChars :: String
symbolChars = "!#$%&|*+-/:<=>?@^_~" ++ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

lispsymbol :: Parser SExpr
lispsymbol = liftM SymbolLiteral (many1 (oneOf symbolChars))

integer :: Parser SExpr
integer = liftM (IntLiteral . Prelude.read) (many1 digit)

float :: Parser SExpr
float = do
  whole <- many1 digit
  char '.'
  fraction <- many1 digit
  return (FloatLiteral (Prelude.read $ whole ++ "." ++ fraction))

number :: Parser SExpr
number = do
  n <- try float <|> integer
  notFollowedBy (oneOf symbolChars)
  return n

listEnd :: Parser [SExpr]
listEnd = return []

listBody :: Parser [SExpr]
listBody = do
  car <- expr
  spaces
  cdr <- try listBody <|> listEnd
  return (car:cdr)

list :: Parser SExpr
list = do
  whitespace
  char '('
  whitespace
  body <- try listBody <|> listEnd
  whitespace
  char ')'
  return (List body)

escapedChar :: Parser Char
escapedChar = (char '\\') >> (oneOf "rtn\\\"")

stringlit :: Parser SExpr
stringlit = do
  char '"'
  contents <- manyTill ((try escapedChar) <|> (noneOf "\"\\")) (char '"')
  return (StringLiteral contents)

comment :: Parser ()
comment = do
  string "--"
  manyTill anyChar ((eof >> return '\n') <|> (char '\n'))
  return ()

comments :: Parser ()
comments = skipMany (comment >> whitespace)

expr :: Parser SExpr
expr = number
       <|> stringlit
       <|> lispsymbol
       <|> list

whitespace :: Parser ()
whitespace = skipMany space

readAll :: Parser [SExpr]
readAll = do
  whitespace
  comments
  result <- many $ do
              e <- expr
              whitespace
              comments
              return e
  eof
  return result

-- Interface

sexprToTerm :: SExpr -> Term
sexprToTerm (IntLiteral i) = TIntLiteral { tirepr=i }
sexprToTerm (FloatLiteral f) = TFloatLiteral { tfrepr=f }
sexprToTerm (SymbolLiteral s) = TName { tsrepr=s }
sexprToTerm (StringLiteral s) = TStringLiteral { tsrepr=s }
sexprToTerm (List (e:es)) = listToTerm e es
sexprToTerm (List []) = error "Function call with no target"

listToTerm :: SExpr -> [SExpr] -> Term
listToTerm (SymbolLiteral "quote") list = TListLiteral (map sexprToTerm list)
listToTerm func args = TFuncall { tfun=(sexprToTerm func), targs=(map sexprToTerm args) }

parseToplevel :: String -> [SExpr]
parseToplevel input = case parse readAll "lisp" input of
                        Left err -> error $ "No match: " ++ show err
                        Right val -> val
