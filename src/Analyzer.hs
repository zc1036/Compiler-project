
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Parser (Term, TType)
import Data.Maybe
import Data.Map.Lazy

type SymbolTable = Map (String, Int) TDef

data AnalyzerTag = TypeTag TType
                 | LambdaTag TType SymbolTable -- The type of the lambda and its lexical variables
                 | Nothing
                   deriving (Show)

type TypedTerm = Term AnalyzerTag

data AnalyzerState = AnalyzerState { symbols :: SymbolTable,       -- A map of declaration names to declarations,
                                     currentScopeLevel :: Int,     -- the current scope level starting from 0 ascending
                                     tterms :: [TypedTerms] }      -- the terms analyzed so far
                     deriving (Show)

analyzerStateTTerms :: AnalyzerState -> [TypedTerms]
analyzerStateTTerms (AnalyzerState { tterms }) = tterms

type AnalyzerResult = [TypedTerm] -- typed terms

-- Builds a default symbol map
defaultSymTable :: SymbolTable
defaultSymTable = 

analyze' :: [Term] -> AnalyzerState -> AnalyzerResult

analyze' [] (AnalyzerState { tterms }) = tterms

analyze' (def@(TDef { tname }):terms) state@(AnalyzerState { symbols, currentScope }) =
    if redeclaration then
        error $ n ++ " redefined"
    else
        analyze' terms (state { symbols=(insert (tname, currentScope) def symbols) })
    where redeclaration = case (lookup tname symbols) of
                            Just (scope, _) -> (scope == currentScope)
                            Nothing -> False

analyze' ((TName { tsrepr }):terms) state@(AnalyzerState { symbols }) =
    if declared then
        analyze' terms state
    else
        error $ "Variable '" ++ tsrepr ++ "' undefined"
    where declared = member tsrepr symbols

analyze' (())

analyze :: [Term] -> AnalyzerResult
analyze terms = reverse (analyzerTypedTerms (analyze' terms $ AnalyzerState empty 0 []))
