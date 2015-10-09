
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

data TType = Ptr TType
           | Mutable TType
           | Function TType [TType] -- rettype [args]
           | Type Term
             deriving (Show)

data Term = TName          { tsrepr :: String }
          | TIntLiteral    { tirepr :: Integer }
          | TFloatLiteral  { tfrepr :: Float }
          | TStringLiteral { tsrepr :: String }
          | TFuncall       { tfun :: Term, targs :: [Term] }
          | TDef           { tname :: String, ttype :: TType, tvalue :: Maybe Term }
          | TLambda        { ttype :: TType, tbindings :: [Term], tbody :: [Term] }
          | TStruct        { tname :: String, tfields :: [Term] }
          | TAssign        { vars :: [Term], value :: Term }
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

sexprToTerm :: SExpr -> Term
sexprToTerm (IntLiteral i) = TIntLiteral { tirepr=i }
sexprToTerm (FloatLiteral f) = TFloatLiteral { tfrepr=f }
sexprToTerm (SymbolLiteral s) = TName { tsrepr=s }
sexprToTerm (StringLiteral s) = TStringLiteral { tsrepr=s }
sexprToTerm (List l) = listToTerm l

listToTerm :: [SExpr] -> Term
listToTerm ((SymbolLiteral "def"):name:t:value:[]) = TDef { tname=name, ttype=(sexprToType t), tvalue=(sexprToTerm value) }
listToTerm ((SymbolLiteral "lambda"):rest) = processLambda rest
listToTerm ((SymbolLiteral "="):rest) = TAssign { vars=(map sexprToTerm $ init rest),
                                                  value=(sexprToTerm $ last rest) }
listToTerm (func:args) = TFuncall { tfun=(sexprToTerm func), targs=(map sexprToTerm args) }

processLambda :: [SExpr] -> Term
processLambda ((List args):rettype:body) = TLambda { ttype=(sexprToType rettype),
                                                     tbindings=(map processLambdaArg args),
                                                     tbody=(map sexprToTerm body) }
processLambda x = error $ "Malformed lambda: " ++ (show x)

processLambdaArg :: SExpr -> Term
processLambdaArg (List ((SymbolLiteral name):argtype:[])) = TDef { tname=name, ttype=(sexprToType argtype), tvalue=Nothing }
processLambdaArg x = error $ "Malformed lambda parameter: " ++ (show x)

sexprToType :: SExpr -> TType
sexprToType (List ((SymbolLiteral "*"):rest:[])) = Ptr (sexprToType rest)
sexprToType (List ((SymbolLiteral "mut"):rest:[])) = Mutable (sexprToType rest)
sexprToType (List (rettype:args)) = Function (sexprToType rettype) (map sexprToType args)
sexprToType x = Type (sexprToTerm x)

-- Interface

parseToplevel :: String -> [Term]
parseToplevel input = case parse readAll "lisp" input of
                        Left err -> error $ "No match: " ++ show err
                        Right val -> (map sexprToTerm val)
