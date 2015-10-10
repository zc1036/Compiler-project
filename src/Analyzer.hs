
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Utils (mapfold, makeMap)
import Parser
import Data.Maybe
import qualified Data.Map.Lazy as Map

type AnalyzerTag = TType
type TypedTerm = Term AnalyzerTag
type SymbolTable = Map.Map String (Term AnalyzerTag, Int)

data AnalyzerState = AnalyzerState { symbols :: SymbolTable, -- A map of declaration names to declarations,
                                     scopeLevel :: Int }     -- the current scope level starting from globalScope ascending
                     deriving (Show)

globalScope :: Int
globalScope = 0

intType = Type "int"
floatType = Type "float"
stringType = Type "string"
typeType = Type "type" -- lol

defaultSymTable :: SymbolTable
defaultSymTable = makeMap [("int", (TBuiltinType { tname="int", tag=typeType }, globalScope)),
                           ("float", (TBuiltinType { tname="float", tag=typeType }, globalScope)),
                           ("string", (TBuiltinType { tname="string", tag=typeType }, globalScope)),
                           ("type", (TBuiltinType { tname="type", tag=typeType }, globalScope))]

isType :: AnalyzerState -> TType -> Bool
isType s (Ptr t) = isType s t
isType s (Mutable t) = isType s t
isType s (Function rettype args) = (isType s rettype) && (foldl (&&) True (map (isType s) args))
isType (AnalyzerState { symbols }) (Type name) =
    case (Map.lookup name symbols) of
      Just (TBuiltinType { }, _) -> True
      Just (TStruct { }, _) -> True
      _ -> False

analyze' :: AnalyzerState -> Term () -> (AnalyzerState, TypedTerm)

analyze' state@(AnalyzerState { symbols, scopeLevel }) def@(TDef { tname, ttype, tvalue }) =
    if redeclaration then
        error $ tname ++ " redefined"
    else if (not (isType state ttype)) then
        error $ (show ttype) ++ " is not a valid type (invalid type name)"
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

--analyze' state@(AnalyzerState { scopeLevel }) (TLambda { rettype, tbindings, tbody }) =
--    case ee

analyze' state (TIntLiteral { tirepr }) = (state, TIntLiteral { tag=intType, tirepr=tirepr })
analyze' state (TFloatLiteral { tfrepr }) = (state, TFloatLiteral { tag=floatType, tfrepr=tfrepr })
analyze' state (TStringLiteral { tsrepr }) = (state, TStringLiteral { tag=intType, tsrepr=tsrepr })

analyze' _ x = error $ "Attempted to analyze invalid form " ++ (show x)

analyze :: [Term ()] -> [TypedTerm]
analyze terms = snd (mapfold analyze' (AnalyzerState { symbols=defaultSymTable, scopeLevel=globalScope }) terms)
