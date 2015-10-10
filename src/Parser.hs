
{-# LANGUAGE NamedFieldPuns #-}

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
           | Type String
             deriving (Show)

-- The type variable "a" stores arbitrary data in the tree structure
data Term a = TName          { tag :: a, tsrepr :: String }
            | TIntLiteral    { tag :: a, tirepr :: Integer }
            | TFloatLiteral  { tag :: a, tfrepr :: Float }
            | TStringLiteral { tag :: a, tsrepr :: String }
            | TFuncall       { tag :: a, tfun :: Term a, targs :: [Term a] }
            | TDef           { tag :: a, tname :: String, ttype :: TType, tvalue :: Maybe (Term a) }
            | TLambda        { tag :: a, ttype :: TType, tbindings :: [Term a], tbody :: [Term a] }
            | TStruct        { tag :: a, tname :: String, tfields :: [Term a] }
            | TAssign        { tag :: a, vars :: [Term a], value :: Term a }
              deriving (Show)

definitionType (TDef { ttype }) = ttype

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

sexprToTerm :: SExpr -> Term ()
sexprToTerm (IntLiteral i) = TIntLiteral { tag=(), tirepr=i }
sexprToTerm (FloatLiteral f) = TFloatLiteral { tag=(), tfrepr=f }
sexprToTerm (SymbolLiteral s) = TName { tag=(), tsrepr=s }
sexprToTerm (StringLiteral s) = TStringLiteral { tag=(), tsrepr=s }
sexprToTerm (List l) = listToTerm l

listToTerm :: [SExpr] -> Term ()
listToTerm ((SymbolLiteral "def"):name:t:value:[]) = case name of
                                                       SymbolLiteral repr ->
                                                           TDef { tag=(),
                                                                  tname=repr,
                                                                  ttype=(sexprToType t),
                                                                  tvalue=Just (sexprToTerm value) }
                                                       _ -> error $ "Expected symbol in definition, got" ++ (show name)
listToTerm ((SymbolLiteral "def"):_) = error "Invalid DEF syntax"

listToTerm ((SymbolLiteral "lambda"):rest) = processLambda rest
listToTerm ((SymbolLiteral "="):rest) = TAssign { tag=(),
                                                  vars=(map sexprToTerm $ init rest),
                                                  value=(sexprToTerm $ last rest) }
listToTerm (func:args) = TFuncall { tag=(), tfun=(sexprToTerm func), targs=(map sexprToTerm args) }
listToTerm [] = error "Empty function call"

processLambda :: [SExpr] -> Term ()
processLambda (rettype:(List args):body) = TLambda { tag=(),
                                                     ttype=(sexprToType rettype),
                                                     tbindings=(map processLambdaArg args),
                                                     tbody=(map sexprToTerm body) }
processLambda x = error $ "Malformed lambda: " ++ (show x)

processLambdaArg :: SExpr -> Term ()
processLambdaArg (List ((SymbolLiteral name):argtype:[])) = TDef { tag=(),
                                                                   tname=name,
                                                                   ttype=(sexprToType argtype),
                                                                   tvalue=Nothing }
processLambdaArg x = error $ "Malformed lambda parameter: " ++ (show x)

sexprToType :: SExpr -> TType
sexprToType (List ((SymbolLiteral "*"):rest:[])) = Ptr (sexprToType rest)
sexprToType (List ((SymbolLiteral "mut"):rest:[])) = Mutable (sexprToType rest)
sexprToType (List (rettype:args)) = Function (sexprToType rettype) (map sexprToType args)
sexprToType (SymbolLiteral s) = Type s
sexprToType x = error $ "Invalid type " ++ (show x)

-- Interface

parseToplevel :: String -> [Term ()]
parseToplevel input = case parse readAll "lisp" input of
                        Left err -> error $ "No match: " ++ show err
                        Right val -> (map sexprToTerm val)
