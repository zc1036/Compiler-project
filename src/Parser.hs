
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

-- The difference between DeclType here and TBuiltinType below is that
-- the DeclTypes are the "objects" and the TBuiltinTypes are the
-- handles/names that refer to those objects. That is to say, a
-- TBuiltinType is an object in the language, but a DeclType is only
-- known to the compiler.

data DeclType = DeclPtr DeclType
              | DeclArray Int DeclType
              | DeclMutable DeclType
              | DeclFunction DeclType [DeclType] -- rettype [args]
              | TypeName String
                deriving (Show)

data LambdaArg = LambdaArg String DeclType
                 deriving (Show)

lambdaArgName :: LambdaArg -> String
lambdaArgName (LambdaArg name _) = name

lambdaArgType :: LambdaArg -> DeclType
lambdaArgType (LambdaArg _ dtype) = dtype

-- The type variable "a" allows storing arbitrary data in the tree
-- structure in the "tag" field
data Term a = TName          { tag :: a, tsrepr :: String }
            | TIntLiteral    { tag :: a, tirepr :: Integer }
            | TFloatLiteral  { tag :: a, tfrepr :: Float }
            | TStringLiteral { tag :: a, tsrepr :: String }
            | TFuncall       { tag :: a, tfun :: Term a, targs :: [Term a] }
            | TDef           { tag :: a, tname :: String, ttype :: DeclType, tvalue :: Maybe (Term a) }
            | TLambda        { tag :: a, rettype :: DeclType, tbindings :: [LambdaArg], tbody :: [Term a] }
            | TStruct        { tag :: a, tfields :: [(String, DeclType)], tname :: String }
            | TAssign        { tag :: a, tavar :: Term a, tavalue :: Term a }
            | TReturn        { tag :: a, tvalue :: Maybe (Term a) }
            | TDeref         { tag :: a, toperand :: Term a }
            | TAddr          { tag :: a, toperand :: Term a }
            | TSubscript     { tag :: a, ttarget :: Term a, tsubscripts :: [Term a] }
            | TMemberAccess  { tag :: a, ttarget :: Term a, tmembers :: [Term a] }
            | TTypedef       { tag :: a, ttypedefFrom :: DeclType, ttypedefTo :: String }
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
listToTerm ((SymbolLiteral "return"):value:[]) = TReturn { tag=(), tvalue=Just (sexprToTerm value) }
listToTerm ((SymbolLiteral "return"):[]) = TReturn { tag=(), tvalue=Nothing }
listToTerm ((SymbolLiteral "struct"):(SymbolLiteral name):fields) = TStruct { tag=(), tname=name, tfields=processStructFields fields }
listToTerm ((SymbolLiteral "="):var:val:[]) = TAssign { tag=(),
                                                        tavar=sexprToTerm var,
                                                        tavalue=sexprToTerm value }
listToTerm ((SymbolLiteral "$"):arg:[]) = TDeref { tag=(), toperand=(sexprToTerm arg) }
listToTerm ((SymbolLiteral "$"):arr:idx:idxs) = TSubscript { tag=(), ttarget=(sexprToTerm arr), tsubscripts=((sexprToTerm idx):(map sexprToTerm idxs)) }
listToTerm x@((SymbolLiteral "$"):_) = error $ "Malformed dereference " ++ (show x)
listToTerm ((SymbolLiteral "@"):arg:[]) = TAddr { tag=(), toperand=(sexprToTerm arg) }
listToTerm x@((SymbolLiteral "@"):_) = error $ "Malformed address-of operand " ++ (show x)
listToTerm ((SymbolLiteral "typedef"):(SymbolLiteral name):from:[]) = TTypedef { tag=(), ttypedefFrom=(sexprToType from), ttypedefTo=name }
listToTerm x@((SymbolLiteral "typedef"):_) = error $ "Malformed typedef " ++ (show x)
listToTerm (func:args) = TFuncall { tag=(), tfun=(sexprToTerm func), targs=(map sexprToTerm args) }
listToTerm [] = error "Empty function call"

processLambda :: [SExpr] -> Term ()
processLambda (rettype:(List args):body) = TLambda { tag=(),
                                                     rettype=(sexprToType rettype),
                                                     tbindings=(map processLambdaArg args),
                                                     tbody=(map sexprToTerm body) }
processLambda x = error $ "Malformed lambda: " ++ (show x)

processLambdaArg :: SExpr -> LambdaArg
processLambdaArg (List ((SymbolLiteral name):argtype:[])) = LambdaArg name (sexprToType argtype)
processLambdaArg x = error $ "Malformed lambda parameter: " ++ (show x)

sexprToType :: SExpr -> DeclType
sexprToType (List ((SymbolLiteral "ptr"):rest:[])) = DeclPtr (sexprToType rest)
sexprToType (List ((SymbolLiteral "mut"):rest:[])) = DeclMutable (sexprToType rest)
sexprToType (List ((IntLiteral size):rest:[])) = DeclArray size (sexprToType rest)
sexprToType (List (rettype:args)) = DeclFunction (sexprToType rettype) (map sexprToType args)
sexprToType (SymbolLiteral s) = TypeName s
sexprToType x = error $ "Invalid type " ++ (show x)

-- Interface

parseToplevel :: String -> [Term ()]
parseToplevel input = case parse readAll "lisp" input of
                        Left err -> error $ "No match: " ++ show err
                        Right val -> (map sexprToTerm val)
