
module Analyzer where

import Parser (Term, TType)
import Data.Maybe
import Data.Map.Lazy

data TypedTerm = TypedTerm { term :: Term, ttype :: TType }

data AnalyzerState = AnalyzerState { symbols :: Map String (Int TDef), -- A map of declaration names to declarations,
                                     currentScope :: Int,              -- the current scope level starting from 0 ascending
                                     tterms :: [TypedTerm] }

-- Simple accessor for AnalyzerState.tterms
analyzerTypedTerms :: AnalyzerState -> [TypedTerm]
analyzerTypedTerms (AnalyzerState { tterms=tterms }) = tterms

-- Builds a default symbol map
defaultSymTable :: Map String (Int TDef)
defaultSymTable = 

-- Returns Nothing on success, Maybe with an error string on failure
analyze' :: [Term] -> AnalyzerState -> AnalyzerResult

analyze' [] state = state

analyze' (def@(TDef { tname=n }):terms) state@(AnalyzerState { symbols=symbols, currentScope=currentScope }) =
    if redeclaration then
        error $ n ++ " redefined"
    else
        analyze' terms (state { symbols=(insert n (currentScope, def) symbols) })
    where redeclaration = case (lookup n symbols) of
                            Just (scope, _) -> (scope == currentScope)
                            Nothing -> False

analyze' ((TName { tsrepr=repr }):terms) state@(AnalyzerState { symbols=symbols }) =
    if declared then
        analyze' terms state
    else
        error $ "Variable '" ++ repr ++ "' undefined"
    where declared = member repr symbols

analyze' (())

analyze :: [Term] -> AnalyzerResult
analyze terms = reverse (analyzerTypedTerms (analyze' terms $ AnalyzerState empty 0 []))
