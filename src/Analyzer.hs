
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Utils (makeMap, recsearch)
import Parser
import Data.Maybe
import qualified Data.Map.Lazy as Map
import Data.List (intercalate, mapAccumL, elemIndex)

data TypeInfo = BuiltinType { typeid :: Int, name :: String }
              | Struct { typeid :: Int, fields :: [(String, DeclType)], parent :: TypeInfo, name :: String }

instance Show TypeInfo where
    show (BuiltinType { name }) = "[builtin " ++ name ++ "]"
    show (Struct { name }) = "[struct " ++ name ++ "]"

instance Eq TypeInfo where
    (==) x y = (typeid x) == (typeid y)

-- After a DeclType has been looked up and verified, it becomes a
-- QualifiedTypeInfo
data QualifiedTypeInfo = Ptr QualifiedTypeInfo
                       | Array Int QualifiedTypeInfo
                       | Mutable QualifiedTypeInfo
                       | Function QualifiedTypeInfo [QualifiedTypeInfo]
                       | Unqualified TypeInfo

functionPtrArgs :: QualifiedTypeInfo -> [QualifiedTypeInfo]
functionPtrArgs (Ptr (Function _ argtypes)) = argtypes
functionPtrArgs x = error $ (show x) ++ " is not a function pointer and so isn't callable"

functionPtrRetType :: QualifiedTypeInfo -> QualifiedTypeInfo
functionPtrRetType (Ptr (Function rettype _)) = rettype
functionPtrRetType x = error $ (show x) ++ " is not a function pointer and so isn't callable"
                                    
instance Show QualifiedTypeInfo where
    show (Ptr x) = (show x) ++ "*"
    show (Array size x) = (show x) ++ "[" ++ (show size) ++ "]"
    show (Mutable x) = "mut " ++ (show x)
    show (Function rettype args) = "(" ++ (intercalate " " (map show args)) ++ " -> " ++ (show rettype) ++ ")"
    show (Unqualified x) = show x

instance Eq QualifiedTypeInfo where
    (==) (Ptr x) (Ptr y) = x == y
    (==) (Array size1 x1) (Array size2 x2) = size1 == size2 && x1 == x2
    (==) (Mutable x) (Mutable y) = x == y
    (==) (Function rettype1 args1) (Function rettype2 args2) =
        rettype1 == rettype2 && (length args1) == (length args2) && (and (zipWith (==) args1 args2))
    (==) (Unqualified x) (Unqualified y) = x == y

-- A "Named" is a thing that is stored in the symbol table.
data Named = Variable QualifiedTypeInfo
           | Type QualifiedTypeInfo
             deriving (Show)

type TypedTerm = Term QualifiedTypeInfo
type SymbolTable = Map.Map String (Named, Int)

data AnalyzerState = AnalyzerState { symbols :: SymbolTable, -- A map of declaration names to declarations,
                                     scopeLevel :: Int,      -- the current scope level starting from globalScope ascending
                                     nextTypeID :: Int }
                     deriving (Show)

globalScope :: Int
globalScope = 0

intTypeID = 0
floatTypeID = 1
charTypeID = 2
voidTypeID = 3
startUserDefinedTypeIDs = voidTypeID + 1

intType = Unqualified (BuiltinType { typeid=intTypeID, name="int" })
floatType = Unqualified (BuiltinType { typeid=floatTypeID, name="float" })
charType = Unqualified (BuiltinType { typeid=charTypeID, name="char" })
voidType = Unqualified (BuiltinType { typeid=voidTypeID, name="void" })
stringType = Ptr charType

defaultSymTable :: SymbolTable
defaultSymTable = makeMap [("int", (Type intType, globalScope)),
                           ("float", (Type floatType, globalScope)),
                           ("char", (Type charType, globalScope)),
                           ("void", (Type voidType, globalScope)),
                           ("string", (Type charTtpe, globalScope))]

isLvalue :: Term a -> Bool
isLvalue (TName { }) = True
isLvalue (TDeref { }) = True
isLvalue (TSubscript { }) = True
isLvalue (TMemberAccess { }) = True
isLvalue _ = False

decltypeToTypeInfo :: AnalyzerState -> DeclType -> QualifiedTypeInfo
decltypeToTypeInfo s (DeclPtr t) = Ptr (decltypeToTypeInfo s t)
decltypeToTypeInfo s (DeclArray size t) = Array size (decltypeToTypeInfo t)
decltypeToTypeInfo s (DeclMutable (DeclMutable _)) = error "Repeated mutability specifier in type"
decltypeToTypeInfo s (DeclMutable (DeclArray _ _)) = error "Cannot declare a mutable array (did you mean array of mutable?)"
decltypeToTypeInfo s (DeclMutable t) = Mutable (decltypeToTypeInfo s t)
decltypeToTypeInfo s (DeclFunction rettype args) = Function (decltypeToTypeInfo s rettype) (map (decltypeToTypeInfo s) args)
decltypeToTypeInfo (AnalyzerState { symbols }) (TypeName name) =
    case Map.lookup name symbols of
      Just (Type t, _) -> t
      _ -> error $ "Undefined typename '" ++ name ++ "'"

-- True if the first argument is compatible with the first (i.e. an
-- object of the first type can be implicitly converted to an object
-- of the second)
typesAreCompatible :: QualifiedTypeInfo -> QualifiedTypeInfo -> Bool
typesAreCompatible (Ptr x) (Array _ y) = typesAreCompatible x y
typesAreCompatible (Ptr x) (Ptr y) = typesAreCompatible x y
typesAreCompatible (Mutable x) (Mutable y) = typesAreCompatible x y
typesAreCompatible x (Mutable y) = typesAreCompatible x y
typesAreCompatible (Unqualified x) (Unqualified y) = x == y
typesAreCompatible (Function rettype1 args1) (Function rettype2 args2) =
    -- Function types have to match exactly; check ret types, arg
    -- counts, and then check each arg type and ensure they match exactly.
    (rettype1 == rettype2) && (length args1) == (length args2) && (and (zipWith (==) args1 args2))
typesAreCompatible _ _ = False

isAssignable :: TypedTerm -> Bool
isAssignable (Mutable _) = True
isAssignable _ = False

isRedeclaration :: String -> SymbolTable -> Int -> Bool
isRedeclaration name symbols scopeLevel = case Map.lookup name symbols of
                                            Just (_, scope) -> (scope == scopeLevel)
                                            _               -> False

analyze' :: AnalyzerState -> Term () -> (AnalyzerState, TypedTerm)

analyze' state@(AnalyzerState { symbols, scopeLevel, nextTypeID }) (TDef { tname, ttype, tvalue })
    | (isRedeclaration tname symbols scopeLevel) = error $ tname ++ " redefined"
    | typesAreIncompatible = error $ "Types " ++ (show typeOfVar) ++ " and " ++ (show (fromJust typeOfValue)) ++ " are incompatible "
    | otherwise = (state { symbols=Map.insert tname (Variable typeOfVar, scopeLevel) symbols, nextTypeID=newNextTypeID },
                   TDef { tag=voidType, tname=tname, ttype=ttype, tvalue=analyzedValue })
    where (newNextTypeID, analyzedValue) = case tvalue of
                                             Just declvalue -> let (substate, analyzed) = analyze' state declvalue
                                                               in ((Analyzer.nextTypeID substate), Just analyzed)
                                             Nothing        -> (nextTypeID, Nothing)
          typeOfVar = (decltypeToTypeInfo state ttype)
          typeOfValue = case analyzedValue of
                          Just declvalue -> Just (tag declvalue)
                          Nothing        -> Nothing
          typesAreIncompatible = case typeOfValue of
                                   Just typeOfValue' -> not (typesAreCompatible typeOfVar typeOfValue')
                                   Nothing           -> False

analyze' state@(AnalyzerState { symbols }) (TName { tsrepr }) =
    case Map.lookup tsrepr symbols of
      Just (Variable vartype, _) -> (state, TName { tsrepr=tsrepr, tag=vartype })
      Just (Type _, _)           -> error $ "Unexpected typename '" ++ tsrepr ++ "'"
      Nothing                    -> error $ "Undefined symbol '" ++ tsrepr ++ "'"

analyze' state@(AnalyzerState { scopeLevel }) (TLambda { rettype, tbindings, tbody }) =
    let rettypeinfo = decltypeToTypeInfo state rettype
        argstypeinfo = (map ((decltypeToTypeInfo state) . lambdaArgType) tbindings)
        lambdaType = (Ptr (Function rettypeinfo argstypeinfo))
        lambdaState = bindLambdaList (state { scopeLevel=(Analyzer.scopeLevel state) + 1 }) tbindings
        (substate, analyzedBody) = analyzeWithState' lambdaState tbody
        wronglyTypedReturnStatement = recsearch (find1 (not . isLambda) (returnIsBad rettypeinfo)) analyzedBody
    in case wronglyTypedReturnStatement of
         Just (TReturn { tvalue=Nothing }) -> error $ "Tried to return nothing from a function returning " ++ (show rettypeinfo)
         Just (TReturn { tvalue=Just val }) -> error $ "Tried to return a " ++ (show (tag val)) ++ " from a function returning " ++ (show rettypeinfo)
         Nothing  -> (state { nextTypeID=nextTypeID substate },
                      TLambda { tag=lambdaType, rettype=rettype, tbindings=tbindings, tbody=analyzedBody })
    where isLambda (TLambda { }) = True
          isLambda _             = False
          returnIsBad good (TReturn { tvalue=Just val }) = not $ typesAreCompatible good (tag val)
          returnIsBad good (TReturn { tvalue=Nothing }) = good /= voidType
          returnIsBad _ _ = False

analyze' state (TReturn { tvalue=Just val }) =
    let (substate, analyzedValue) = analyze' state val
    in (state { nextTypeID=nextTypeID substate },
        TReturn { tag=voidType, tvalue=Just analyzedValue })

analyze' state (TFuncall { tfun, targs }) =
    let (substate, analyzedFunName) = analyze' state tfun
        (substate', analyzedArgs) = analyzeWithState' substate targs
        paramTypes = functionPtrArgs (tag analyzedFunName)
        argTypes = (map tag analyzedArgs) in
    if length argTypes /= length paramTypes then
        error $ "Wrong number of arguments to function " ++ (show tfun) ++ ": expecting " ++ (show (length paramTypes)) ++ ", got " ++ (show (length argTypes))
    else
        case elemIndex False (zipWith typesAreCompatible argTypes paramTypes) of
          Just idx -> error $ "Function argument " ++ (show (targs !! idx)) ++ ", which is of type " ++ (show (tag (analyzedArgs !! idx))) ++ ", is incompatible with type of parameter " ++ (show (idx + 1)) ++ " of " ++ (show tfun) ++ ", " ++ (show ((functionPtrArgs (tag analyzedFunName)) !! idx))
          Nothing  -> (substate', TFuncall { tag=functionPtrRetType (tag analyzedFunName),
                                             tfun=analyzedFunName,
                                             targs=analyzedArgs })

analyze' state (TAssign { tavar, tavalue }) =
    let (substate, analyzedVar) = analyzeWithState' state tavar
        (substate', analyzedValue) = analyze' substate tavalue in
    if typesAreCompatible analyzedVar analyzedValue && isAssignable (tag tavar) && isLvalue tavar then
        (state, TAssign { tag=tag tavar, tavar=analyzedVar, tavalue=analyzedValue })
    else
        error $ "Illegal assignment to " ++ (show analyzedVar) ++ " of " ++ (show analyzedVar)

analyze' state@(AnalyzerState { symbols, scopeLevel }) (TTypedef { ttypedefFrom, ttypedefTo })
    | isRedeclaration ttypedefTo symbols scope = error $ "Duplicate declaration of " ++ ttypedefTo ++ " in typedef"
    | otherwise = let newType = decltypeToTypeInfo state ttypedefFrom in
                  (state { symbols=Map.insert ttypedefTo (Type newType, scopeLevel) symbols },
                   TTypedef { tag=voidType, ttypedefFrom=ttypedefFrom, ttypedefTo=ttypedefTo })

analyze' state@(AnalyzerState { symbols, scopeLevel, nextTypeID }) (TStruct { tfields, tname })
    | isRedeclaration tname symbols scopeLevel = error $ "Duplicate declaration of " ++ tname ++ " in struct definition"
    | otherwise = 

analyze' state (TReturn { tvalue=Nothing }) =
    (state, TReturn { tag=voidType, tvalue=Nothing })

analyze' state (TIntLiteral { tirepr }) = (state, TIntLiteral { tag=intType, tirepr=tirepr })
analyze' state (TFloatLiteral { tfrepr }) = (state, TFloatLiteral { tag=floatType, tfrepr=tfrepr })
analyze' state (TStringLiteral { tsrepr }) = (state, TStringLiteral { tag=stringType, tsrepr=tsrepr })

analyze' _ x = error $ "Attempted to analyze unrecognized form " ++ (show x)

-- Expects the scope level to have already been incremented
bindLambdaList :: AnalyzerState -> [LambdaArg] -> AnalyzerState
bindLambdaList state [] = state
bindLambdaList state@(AnalyzerState { symbols }) (arg:args) =
    bindLambdaList (state { symbols=Map.insert (lambdaArgName arg)
                                               (Variable (decltypeToTypeInfo state (lambdaArgType arg)), (scopeLevel state))
                                               symbols }) args

find1 :: (Term a -> Bool) -> (Term a -> Bool) -> Term a -> Maybe (Term a)
find1 _ f t@(TName { }) = if f t then Just t else Nothing
find1 _ f t@(TIntLiteral { }) = if f t then Just t else Nothing
find1 _ f t@(TFloatLiteral { }) = if f t then Just t else Nothing
find1 _ f t@(TStringLiteral { }) = if f t then Just t else Nothing
find1 p f t@(TStruct { }) = if f t then Just t else Nothing
find1 p f t@(TFuncall { tfun, targs })
    | f t = (Just t)
    | p t = recsearch (find1 p f) (tfun:targs)
    | otherwise = Nothing
find1 p f t@(TDef { tvalue=Just x })
    | f t = Just t
    | p t = find1 p f x
    | otherwise = Nothing
find1 _ f t@(TDef { }) = if f t then Just t else Nothing
find1 p f t@(TLambda { tbody })
    | f t = Just t
    | p t = recsearch (find1 p f) tbody
    | otherwise = Nothing
find1 p f t@(TAssign { vars, value })
    | f t = Just t
    | p t = recsearch (find1 p f) (value:vars)
    | otherwise = Nothing
find1 p f t@(TReturn { tvalue=Just x })
    | f t = Just t
    | p t = find1 p f x
    | otherwise = Nothing
find1 p f t@(TReturn { tvalue=Nothing })
    | f t = Just t
    | otherwise = Nothing

analyze :: [Term ()] -> [TypedTerm]
analyze terms = snd (analyzeWithState terms)

analyzeWithState :: [Term ()] -> (AnalyzerState, [TypedTerm])
analyzeWithState terms = analyzeWithState'
                         (AnalyzerState { symbols=defaultSymTable,
                                          scopeLevel=globalScope,
                                          nextTypeID=startUserDefinedTypeIDs })
                         terms

analyzeWithState' :: AnalyzerState -> [Term ()] -> (AnalyzerState, [TypedTerm])
analyzeWithState' state terms = mapAccumL analyze' state terms
