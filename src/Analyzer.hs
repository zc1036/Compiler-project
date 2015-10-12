
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Utils (mapfold, makeMap)
import Parser
import Data.Maybe
import qualified Data.Map.Lazy as Map
import Data.List (intercalate)

data TypeInfo = BuiltinType { typeid :: Int, name :: String }
              | Struct { typeid :: Int, fields :: [(String, DeclType)], parent :: TypeInfo, name :: String }

instance Show TypeInfo where
    show (BuiltinType { name }) = "[builtin " ++ name ++ "]"
    show (Struct { name }) = "[struct " ++ name ++ "]"

-- After a DeclType has been looked up and verified, it becomes a
-- QualifiedTypeInfo
data QualifiedTypeInfo = Ptr QualifiedTypeInfo
                       | Mutable QualifiedTypeInfo
                       | Function QualifiedTypeInfo [QualifiedTypeInfo]
                       | Unqualified TypeInfo

instance Show QualifiedTypeInfo where
    show (Ptr x) = (show x) ++ "*"
    show (Mutable x) = "mut " ++ (show x)
    show (Function rettype args) = "(" ++ (intercalate " " (map show args)) ++ " -> " ++ (show rettype)
    show (Unqualified x) = show x

-- A "Name" is a thing that is stored in the symbol table.
data Name = Variable QualifiedTypeInfo
          | Type TypeInfo
            deriving (Show)

type TypedTerm = Term QualifiedTypeInfo
type SymbolTable = Map.Map String (Name, Int)

data AnalyzerState = AnalyzerState { symbols :: SymbolTable, -- A map of declaration names to declarations,
                                     scopeLevel :: Int,      -- the current scope level starting from globalScope ascending
                                     nextTypeID :: Int }
                     deriving (Show)

globalScope :: Int
globalScope = 0

intTypeID = 0
floatTypeID = 1
stringTypeID = 2
voidTypeID = 3
startUserDefinedTypeIDs = voidTypeID + 1

intType = BuiltinType { typeid=intTypeID, name="int" }
floatType = BuiltinType { typeid=floatTypeID, name="float" }
stringType = BuiltinType { typeid=stringTypeID, name="string" }
voidType = BuiltinType { typeid=voidTypeID, name="void" }

defaultSymTable :: SymbolTable
defaultSymTable = makeMap [("int", (Type intType, globalScope)),
                           ("float", (Type floatType, globalScope)),
                           ("string", (Type stringType, globalScope))]

decltypeToTypeInfo :: AnalyzerState -> DeclType -> QualifiedTypeInfo
decltypeToTypeInfo s (DeclPtr t) = Ptr (decltypeToTypeInfo s t)
decltypeToTypeInfo s (DeclMutable (DeclMutable _)) = error "Repeated mutability specifier in type"
decltypeToTypeInfo s (DeclMutable t) = Mutable (decltypeToTypeInfo s t)
decltypeToTypeInfo s (DeclFunction rettype args) = Function (decltypeToTypeInfo s rettype) (map (decltypeToTypeInfo s) args)
decltypeToTypeInfo (AnalyzerState { symbols }) (TypeName name) =
    case (Map.lookup name symbols) of
      Just (Type t, _) -> Unqualified t
      _ -> error $ "Undefined typename '" ++ name ++ "'"

analyze' :: AnalyzerState -> Term () -> (AnalyzerState, TypedTerm)

analyze' state@(AnalyzerState { symbols, scopeLevel, nextTypeID }) (TDef { tname, ttype, tvalue }) =
    if redeclaration then
        error $ tname ++ " redefined"
    else
        (state { symbols=(Map.insert tname (Variable (decltypeToTypeInfo state ttype), scopeLevel) symbols), nextTypeID=newNextTypeID },
         TDef { tag=(Unqualified voidType), tname=tname, ttype=ttype, tvalue=analyzedValue })
    where redeclaration = case (Map.lookup tname symbols) of
                            Just (_, scope) -> (scope == scopeLevel)
                            _ -> False
          (newNextTypeID, analyzedValue) = fromMaybe (nextTypeID, Nothing) (do tvalue <- tvalue
                                                                               let (substate, analyzed) = analyze' state tvalue
                                                                               return ((Analyzer.nextTypeID substate), Just analyzed))

analyze' state@(AnalyzerState { symbols }) (TName { tsrepr }) =
    case (Map.lookup tsrepr symbols) of
      Just (Variable vartype, _) -> (state, TName { tsrepr=tsrepr, tag=vartype })
      Just (Type _, _)           -> error $ "Unexpected typename '" ++ tsrepr ++ "'"
      Nothing                    -> error $ "Undefined symbol '" ++ tsrepr ++ "'"

--analyze' state@(AnalyzerState { scopeLevel }) (TLambda { rettype, tbindings, tbody }) =
--    case ee

analyze' state (TIntLiteral { tirepr }) = (state, TIntLiteral { tag=(Unqualified intType), tirepr=tirepr })
analyze' state (TFloatLiteral { tfrepr }) = (state, TFloatLiteral { tag=(Unqualified floatType), tfrepr=tfrepr })
analyze' state (TStringLiteral { tsrepr }) = (state, TStringLiteral { tag=(Unqualified stringType), tsrepr=tsrepr })

analyze' _ x = error $ "Attempted to analyze unrecognized form " ++ (show x)

analyze :: [Term ()] -> [TypedTerm]
analyze terms = snd (analyzeWithState terms)

analyzeWithState :: [Term ()] -> (AnalyzerState, [TypedTerm])
analyzeWithState terms = mapfold
                         analyze' (AnalyzerState { symbols=defaultSymTable,
                                                   scopeLevel=globalScope,
                                                   nextTypeID=startUserDefinedTypeIDs })
                         terms
