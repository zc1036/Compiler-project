
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Utils (mapfold)
import Parser
import Data.Maybe
import qualified Data.Map.Lazy as Map

type SymbolTable = Map.Map String (Term (), Int)
type AnalyzerTag = TType
type TypedTerm = Term AnalyzerTag

data AnalyzerState = AnalyzerState { symbols :: SymbolTable,       -- A map of declaration names to declarations,
                                     scopeLevel :: Int }    -- the current scope level starting from 0 ascending
                     deriving (Show)

defaultSymTable :: SymbolTable
defaultSymTable = Map.empty

intType :: TType
intType = Type "int"

analyze' :: AnalyzerState -> Term () -> (AnalyzerState, TypedTerm)

analyze' state@(AnalyzerState { symbols, scopeLevel }) def@(TDef { tname, ttype, tvalue }) =
    if redeclaration then
        error $ tname ++ " redefined"
    else
        (state { symbols=(Map.insert tname (def, scopeLevel) symbols) },
         TDef { tag=ttype, tname=tname, ttype=ttype, tvalue=analyzedValue })
    where redeclaration = case (Map.lookup tname symbols) of
                            Nothing -> False
                            Just (_, scope) -> (scope == scopeLevel)
          analyzedValue = case tvalue of
                            Nothing -> Nothing
                            Just value -> Just $ snd (analyze' state value)

analyze' state@(AnalyzerState { symbols }) (TName { tsrepr }) =
    case (Map.lookup tsrepr symbols) of
      Just (def, _) -> (state, TName { tsrepr=tsrepr, tag=(definitionType def) })
      Nothing       -> error $ "Variable '" ++ tsrepr ++ "' undefined"

analyze' state (TIntLiteral { tirepr }) = (state, TIntLiteral { tag=intType, tirepr=tirepr })

analyze' _ x = error $ "Attempted to analyze invalid form " ++ (show x)

analyze :: [Term ()] -> [TypedTerm]
analyze terms = snd (mapfold analyze' (AnalyzerState { symbols=defaultSymTable, scopeLevel=0 }) terms)
