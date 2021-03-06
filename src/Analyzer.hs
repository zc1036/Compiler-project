
{-# LANGUAGE NamedFieldPuns #-}

module Analyzer where

import Utils (makeMap, recsearch)
import Parser
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.List (intercalate, mapAccumL, elemIndex, findIndex, lookup)
import qualified Data.Set as Set
import Text.Printf

data TypeInfo = BuiltinType { typeid :: Int, name :: String }
              | Struct { typeid :: Int, fields :: [(String, QualifiedTypeInfo)], fieldOffsets :: [Integer], name :: String }

instance Show TypeInfo where
    show (BuiltinType { name }) = "[builtin " ++ name ++ "]"
    show (Struct { name }) = "[struct " ++ name ++ "]"

instance Eq TypeInfo where
    (==) x y = (typeid x) == (typeid y)

-- After a DeclType has been looked up and verified, it becomes a
-- QualifiedTypeInfo
data QualifiedTypeInfo = Ptr QualifiedTypeInfo
                       | Array Integer QualifiedTypeInfo
                       | Mutable QualifiedTypeInfo
                       | Function QualifiedTypeInfo [QualifiedTypeInfo]
                       | Unqualified TypeInfo

memberOffset :: QualifiedTypeInfo -> String -> Int
memberOffset (Mutable x) fieldname = memberOffset x fieldname
memberOffset (Unqualified (Struct { fields, fieldOffsets })) fieldname =
    fromIntegral $ fieldOffsets !! (fromJust $ findIndex (\x -> fst x == fieldname) fields)
memberOffset x _ = error $ "Unexpected type given to memberOffset: " ++ (show x)

functionPtrArgs :: QualifiedTypeInfo -> [QualifiedTypeInfo]
functionPtrArgs (Ptr (Function _ argtypes)) = argtypes
functionPtrArgs x = error $ (show x) ++ " is not a function pointer and so isn't callable"

functionPtrRetType :: QualifiedTypeInfo -> QualifiedTypeInfo
functionPtrRetType (Ptr (Function rettype _)) = rettype
functionPtrRetType x = error $ (show x) ++ " is not a function pointer and so isn't callable"
                                    
instance Show QualifiedTypeInfo where
    show (Ptr x) = "ptr " ++ (show x)
    show (Array size x) = (show x) ++ "[" ++ (show size) ++ "]"
    show (Mutable x) = "mut-" ++ (show x)
    show (Function rettype args) = "(" ++ (intercalate " " (map show args)) ++ " -> " ++ (show rettype) ++ ")"
    show (Unqualified x) = show x

instance Eq QualifiedTypeInfo where
    (==) (Ptr x) (Ptr y) = x == y
    (==) (Array size1 x1) (Array size2 x2) = size1 == size2 && x1 == x2
    (==) (Mutable x) (Mutable y) = x == y
    (==) (Function rettype1 args1) (Function rettype2 args2) =
        rettype1 == rettype2 && (length args1) == (length args2) && (and (zipWith (==) args1 args2))
    (==) (Unqualified x) (Unqualified y) = x == y
    (==) _ _ = False

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

-- Combines two states when the LHS is from a higher lexical scope
-- than the RHS. The same convention is used in other modules as well.
(↖) :: AnalyzerState -> AnalyzerState -> AnalyzerState
(↖) state (AnalyzerState { nextTypeID=newNextTypeID }) = state { nextTypeID=newNextTypeID }

globalScope :: Int
globalScope = 0

intTypeID = 0
floatTypeID = 1
charTypeID = 2
voidTypeID = 3
nullTypeID = 4
startUserDefinedTypeIDs = nullTypeID + 1

intType = Unqualified (BuiltinType { typeid=intTypeID, name="int" })
floatType = Unqualified (BuiltinType { typeid=floatTypeID, name="float" })
charType = Unqualified (BuiltinType { typeid=charTypeID, name="char" })
voidType = Unqualified (BuiltinType { typeid=voidTypeID, name="void" })
nullType = Unqualified (BuiltinType { typeid=nullTypeID, name="null" })
stringType = Ptr charType

defaultSymTable :: SymbolTable
defaultSymTable = makeMap [("int", (Type intType, globalScope)),
                           ("float", (Type floatType, globalScope)),
                           ("char", (Type charType, globalScope)),
                           ("void", (Type voidType, globalScope)),
                           ("string", (Type stringType, globalScope)),
                           ("null", (Variable nullType, globalScope))]

isLvalue :: Term a -> Bool
isLvalue (TName { }) = True
isLvalue (TDeref { }) = True
isLvalue (TSubscript { }) = True
isLvalue (TMemberAccess { }) = True
isLvalue _ = False

pointerSize = 8
intSize = 8
charSize = 1
floatSize = 8

sizeFromType :: QualifiedTypeInfo -> Integer
sizeFromType (Mutable x) = sizeFromType x
sizeFromType (Ptr _) = pointerSize
sizeFromType (Array count atype) = count * (sizeFromType atype)
sizeFromType t@(Unqualified (BuiltinType { typeid }))
    | typeid == intTypeID = intSize
    | typeid == charTypeID = charSize
    | typeid == floatTypeID = floatSize
    | typeid == voidTypeID = error "void has no size"
    | typeid == nullTypeID = pointerSize
    | otherwise = error $ "Unexpected builtin type " ++ (show t)
sizeFromType (Unqualified (Struct { fields })) = max 1 $ foldl (+) 0 $ map (sizeFromType . snd) fields
sizeFromType (Function { }) = error "Functions have no size"

decltypeToTypeInfo :: AnalyzerState -> DeclType -> QualifiedTypeInfo
decltypeToTypeInfo s (DeclPtr t) = Ptr (decltypeToTypeInfo s t)
decltypeToTypeInfo s (DeclArray size t) = let arrtype@(Array _ elemtype) = Array size (decltypeToTypeInfo s t) in
                                          if elemtype == voidType then error "Cannot declare array of void"
                                          else arrtype
decltypeToTypeInfo s (DeclMutable (DeclMutable _)) = error "Repeated mutability specifier in type"
decltypeToTypeInfo s (DeclMutable (DeclArray _ _)) = error "Cannot declare a mutable array (did you mean array of mutable?)"
decltypeToTypeInfo s (DeclMutable t) = let mut@(Mutable mtype) = Mutable (decltypeToTypeInfo s t) in
                                       if mtype == voidType then error "Cannot declare mutable void"
                                       else mut
decltypeToTypeInfo s (DeclFunction rettype args) = Function (decltypeToTypeInfo s rettype) (map (decltypeToTypeInfo s) args)
decltypeToTypeInfo (AnalyzerState { symbols }) (TypeName name) =
    case Map.lookup name symbols of
      Just (Type t, _) -> t
      _ -> error $ "Undefined typename '" ++ name ++ "'"

-- True iff the first argument is compatible with the first (i.e. a
-- pointer to an object of the first type can be implicitly converted
-- to a pointer to an object of the second)
typesAreCompatible :: QualifiedTypeInfo -> QualifiedTypeInfo -> Bool
typesAreCompatible (Ptr x) (Ptr y) = typesAreCompatible x y
typesAreCompatible (Mutable x) (Mutable y) = typesAreCompatible x y
typesAreCompatible x (Mutable y) = typesAreCompatible x y
typesAreCompatible lhs@(Unqualified x) (Unqualified y) = lhs /= voidType && x == y
typesAreCompatible (Function rettype1 args1) (Function rettype2 args2) =
    -- Function types have to match exactly; check ret types, arg
    -- counts, and then check each arg type and ensure they match exactly.
    (rettype1 == rettype2) && (length args1) == (length args2) && (and (zipWith (==) args1 args2))
typesAreCompatible _ _ = False

-- True iff the types fit special conversion rules (i.e. int to pointer, etc)
typesAreConvertible :: QualifiedTypeInfo -> QualifiedTypeInfo -> Bool
typesAreConvertible (Ptr _) (Unqualified (BuiltinType { typeid })) = typeid == nullTypeID
typesAreConvertible _ _ = False

isInitializeableBy :: QualifiedTypeInfo -> QualifiedTypeInfo -> Bool
isInitializeableBy x y = (typesAreCompatible (removeMutability x) y) || (typesAreConvertible (removeMutability x) (removeMutability y))

isMutable :: QualifiedTypeInfo -> Bool
isMutable (Mutable _) = True
isMutable _ = False

isImmutable :: QualifiedTypeInfo -> Bool
isImmutable = not . isMutable

removeMutability :: QualifiedTypeInfo -> QualifiedTypeInfo
removeMutability (Mutable x) = x
removeMutability x = x

isIntegral :: QualifiedTypeInfo -> Bool
isIntegral (Unqualified (BuiltinType { typeid }))
    | typeid == intTypeID = True
    | typeid == charTypeID = True
    | otherwise = False
isIntegral _ = False

isRedeclaration :: String -> SymbolTable -> Int -> Bool
isRedeclaration name symbols scopeLevel = case Map.lookup name symbols of
                                            Just (_, scope) -> (scope == scopeLevel)
                                            _               -> False

analyze' :: AnalyzerState -> Term () -> (AnalyzerState, TypedTerm)

analyze' state@(AnalyzerState { symbols, scopeLevel, nextTypeID }) (TDef { tname, ttype, tvalue })
    | (isRedeclaration tname symbols scopeLevel) = error $ tname ++ " redefined"
    | initializerTypeError = error $ "Types " ++ (show typeOfVar) ++ " and " ++ (show (fromJust typeOfValue)) ++ " are incompatible "
    | otherwise = (newstate ↖ substate,
                   TDef { tag=voidType, vartag=typeOfVar, tname=tname, ttype=ttype, tvalue=analyzedValue })
    where newstate = (state { symbols=Map.insert tname (Variable typeOfVar, scopeLevel) symbols })
          (substate, analyzedValue) = case tvalue of
                                        -- Analyze the initialization after adding the definition to the symbol table
                                        Just declvalue -> let (substate, analyzed) = analyze' newstate declvalue
                                                          in (substate, Just analyzed)
                                        Nothing        -> (state, Nothing)
          typeOfVar = let vartype = (decltypeToTypeInfo state ttype) in
                      if vartype == voidType then error "Cannot declare variable of type void"
                      else vartype
          typeOfValue = case analyzedValue of
                          Just declvalue -> Just (tag declvalue)
                          Nothing        -> Nothing
          initializerTypeError = case typeOfValue of
                                   Just typeOfValue' -> not (isInitializeableBy typeOfVar typeOfValue')
                                   Nothing           -> False

analyze' state@(AnalyzerState { symbols }) (TName { tsrepr }) =
    case Map.lookup tsrepr symbols of
      Just (Variable vartype, _) -> (state, TName { tsrepr=tsrepr, tag=vartype })
      Just (Type _, _)           -> error $ "Unexpected typename '" ++ tsrepr ++ "'"
      Nothing                    -> error $ "Symbol '" ++ tsrepr ++ "' not in scope"

analyze' state@(AnalyzerState { scopeLevel, symbols }) (TLambda { rettype, tbindings, tbody }) =
    let rettypeinfo = decltypeToTypeInfo state rettype
        argstypeinfo = (map ((decltypeToTypeInfo state) . ttype) tbindings)
        lambdaType = (Ptr (Function rettypeinfo argstypeinfo))
        (lambdaState, analyzedBindings) = analyzeWithState' (state { scopeLevel=scopeLevel + 1,
                                                                     symbols=symbolTableWithoutLocalValues }) tbindings
        (substate, analyzedBody) = analyzeWithState' lambdaState tbody
        wronglyTypedReturnStatement = recsearch (find1 (not . isLambda) (returnIsBad rettypeinfo)) analyzedBody
    in case wronglyTypedReturnStatement of
         Just (TReturn { tvalue=Nothing }) -> error $ "Tried to return nothing from a function returning " ++ (show rettypeinfo)
         Just (TReturn { tvalue=Just val }) -> error $ "Tried to return a " ++ (show (tag val)) ++ " from a function returning " ++ (show rettypeinfo)
         Nothing  -> (state ↖ substate,
                      TLambda { tag=lambdaType, rettype=rettype, tbindings=analyzedBindings, tbody=analyzedBody })
    where isLambda (TLambda { }) = True
          isLambda _             = False
          returnIsBad good (TReturn { tvalue=Just val }) = not $ isInitializeableBy good (tag val)
          returnIsBad good (TReturn { tvalue=Nothing }) = good /= voidType
          returnIsBad _ _ = False
          symbolTableWithoutLocalValues = Map.filter filterSymbolTable symbols
          filterSymbolTable (Type _, _) = True
          filterSymbolTable (Variable x, scope) = scope == globalScope

analyze' state (TReturn { tvalue=Just val }) =
    let (substate, analyzedValue) = analyze' state val
    in (state ↖ substate,
        TReturn { tag=voidType, tvalue=Just analyzedValue })

analyze' state (TFuncall { tfun, targs }) =
    let (substate, analyzedFunName) = analyze' state tfun
        (substate', analyzedArgs) = analyzeWithState' (state ↖ substate) targs
        paramTypes = functionPtrArgs (tag analyzedFunName)
        argTypes = (map tag analyzedArgs) in
    if length argTypes /= length paramTypes then
        error $ "Wrong number of arguments to function " ++ (show tfun) ++ ": expecting " ++ (show (length paramTypes)) ++ ", got " ++ (show (length argTypes))
    else
        case elemIndex False (zipWith isInitializeableBy paramTypes argTypes) of
          Just idx -> error $ printf "Function argument %s, which is of type %s, is incompatible with type of parameter %d of %s, %s" (show (targs !! idx)) (show (tag (analyzedArgs !! idx))) (show (idx + 1)) (show tfun) (show ((functionPtrArgs (tag analyzedFunName)) !! idx))
          Nothing  -> (state ↖ substate',
                       TFuncall { tag=functionPtrRetType (tag analyzedFunName),
                                  tfun=analyzedFunName,
                                  targs=analyzedArgs })

analyze' state@(AnalyzerState { symbols }) (TStructLiteral { tstructname, tfieldvalues }) =
    case Map.lookup tstructname symbols of
      Just ((Type littype@(Unqualified (Struct { fields }))), _) ->
          let (newstate, analyzedFieldValues) = analyzeFieldValues state fields tfieldvalues in
          (state ↖ newstate, TStructLiteral { tag=littype, tstructname=tstructname, tfieldvalues=analyzedFieldValues })
      Nothing -> error $ "Name '" ++ tstructname ++ "' is undeclared"
      _ -> error $ tstructname ++ " in structure literal is not a structure"
    where analyzeFieldValues state fields tfieldvalues = let ((finalstate, _), anavalues) = mapAccumL (analyzeFieldValues' fields) (state, Set.empty) tfieldvalues in
                                                         (finalstate, anavalues)
          -- the analyzeFieldValues' function has to check that the
          -- fields of the struct are all initialized exactly once and
          -- that they're initialized with the right type.
          analyzeFieldValues' structFields (state, fieldsAssigned) (fieldname, fieldinit)
              | Set.member fieldname fieldsAssigned = error $ "Member " ++ fieldname ++ " is already initialized in " ++ tstructname ++ " structure literal"
              | otherwise = case lookup fieldname structFields of
                              Just declaredFieldType -> let (newstate, analyzedInitializer) = analyze' state fieldinit
                                                        in if isInitializeableBy declaredFieldType (tag analyzedInitializer)
                                                           then ((newstate, (Set.insert fieldname fieldsAssigned)), (fieldname, analyzedInitializer))
                                                           else error $ printf "Value of type %s cannot be used to initialize field %s of type %s in struct %s (in structure literal)" (show (tag analyzedInitializer)) fieldname (show declaredFieldType) tstructname
                              _ -> error $ "Structure " ++ tstructname ++ " has no member named " ++ fieldname ++ " (in structure literal)"

analyze' state (TMemberAccess { ttarget, tmember }) =
    let (newstate, analyzedTarget) = analyze' state ttarget in
    (state ↖ newstate, memberAccess analyzedTarget (tag analyzedTarget))
    -- memberAccess builds up pointer dereferences until it gets to
    -- the underlying struct type, then returns a TMemberAccess to the
    -- member.
    where memberAccess term (Unqualified (Struct { fields, name=structName })) =
              case lookup tmember fields of
                Just fieldType -> TMemberAccess { tag=fieldType, ttarget=term, tmember=tmember }
                _ -> error $ "Structure of type " ++ structName ++ " has no member named " ++ tmember
          memberAccess term (Mutable unqualified@(Unqualified (Struct { }))) = let access = memberAccess term unqualified in
                                                                               access { tag=Mutable (tag access) }
          memberAccess term (Mutable mtype) = memberAccess term mtype
          memberAccess term (Ptr target) = memberAccess (TDeref { tag=target, toperand=term }) target
          memberAccess _ badtype = error $ "Can't access member " ++ tmember ++ " of object of type " ++ (show badtype) ++ ": is not a structure"

analyze' state (TAssign { tavar, tavalue }) =
    let (substate, analyzedVar) = analyze' state tavar
        (substate', analyzedValue) = analyze' (state ↖ substate) tavalue in
    if isInitializeableBy (tag analyzedVar) (tag analyzedValue) && isMutable (tag analyzedVar) && isLvalue tavar then
        (state ↖ substate', TAssign { tag=tag analyzedVar, tavar=analyzedVar, tavalue=analyzedValue })
    else
        error $ "Illegal assignment to " ++ (show analyzedVar) ++ " of " ++ (show analyzedVar)

analyze' state@(AnalyzerState { symbols, scopeLevel }) (TTypedef { ttypedefFrom, ttypedefTo })
    | isRedeclaration ttypedefTo symbols scopeLevel = error $ "Duplicate declaration of " ++ ttypedefTo ++ " in typedef"
    | otherwise = let newType = decltypeToTypeInfo state ttypedefFrom in
                  (state { symbols=Map.insert ttypedefTo (Type newType, scopeLevel) symbols },
                   TTypedef { tag=voidType, ttypedefFrom=ttypedefFrom, ttypedefTo=ttypedefTo })

analyze' state@(AnalyzerState { symbols, scopeLevel, nextTypeID }) (TStruct { tfields, tname })
    | isRedeclaration tname symbols scopeLevel = error $ "Duplicate declaration of " ++ tname ++ " in struct definition"
    | otherwise = (newstate, TStruct { tag=voidType, tfields=tfields, tname=tname })
    where newstate = state { symbols=Map.insert tname (Type (Unqualified (Struct { typeid=nextTypeID,
                                                                                   fields=processedFields,
                                                                                   fieldOffsets=snd $ mapAccumL calcFieldOffset 0 $ map snd processedFields, 
                                                                                   name=tname })), scopeLevel) symbols,
                             nextTypeID=nextTypeID + 1 }
          processedFields = map processField tfields
          processField (name, decltype) = (name, checkFieldType name $ decltypeToTypeInfo newstate decltype)
          checkFieldType name (Mutable _) = error $ "Cannot specify mutability of structure member " ++ name ++ " in definition of struct " ++ tname
          checkFieldType _ t = t
          calcFieldOffset offset t = let memberSize = (sizeFromType t)
                                         padding = (memberSize - (offset `mod` memberSize)) `mod` memberSize
                                     in (offset + padding + memberSize, offset)

analyze' state (TReturn { tvalue=Nothing }) = (state, TReturn { tag=voidType, tvalue=Nothing })

analyze' state (TDeref { toperand }) =
    let (newstate, analyzedOp) = analyze' state toperand in
    (state ↖ newstate, TDeref { tag=derefType (tag analyzedOp), toperand=analyzedOp })
    where derefType (Mutable (Ptr x)) = checkDerefType x
          derefType (Ptr x) = checkDerefType x
          derefType x = error $ "Attempted to dereference non-pointer type " ++ (show x)
          checkDerefType x = if x == voidType then error "Cannot dereference pointer to void"
                             else x

analyze' state (TAddr { toperand }) =
    let (newstate, analyzedOp) = analyze' state toperand in
    if isLvalue analyzedOp then
        (state ↖ newstate, TAddr { tag=Ptr (tag analyzedOp), toperand=analyzedOp })
    else
        error "Cannot take address of non-lvalue"

analyze' state (TIntLiteral { tirepr }) = (state, TIntLiteral { tag=intType, tirepr=tirepr })
analyze' state (TFloatLiteral { tfrepr }) = (state, TFloatLiteral { tag=floatType, tfrepr=tfrepr })
analyze' state (TStringLiteral { tsrepr }) = (state, TStringLiteral { tag=stringType, tsrepr=tsrepr })

analyze' state subscript@(TSubscript { ttarget, tsubscript }) =
    case validDereferencePattern (tag analyzedTarget) (tag analyzedSubscript) of
      Nothing           -> error $ "Invalid dereference in " ++ (show subscript)
      Just dereffedType -> (state ↖ newstate', TSubscript { tag=dereffedType,
                                                            ttarget=analyzedTarget,
                                                            tsubscript=analyzedSubscript })
    where (newstate, analyzedTarget) = analyze' state ttarget
          (newstate', analyzedSubscript) = analyze' (state ↖ newstate) tsubscript
          validDereferencePattern (Mutable x) idx = validDereferencePattern x idx
          validDereferencePattern (Ptr target) idx = if isIntegral idx
                                                     then Just target
                                                     else Nothing
          validDereferencePattern (Array _ target) idx = if isIntegral idx
                                                         then Just target
                                                         else Nothing
          validDereferencePattern _ _ = Nothing

analyze' state (TWhileLoop { tcondition, tbody }) =
    let (substate, analyzedCondition) = analyze' (state { scopeLevel=(scopeLevel state) + 1 }) tcondition
        (substate', analyzedBody) = analyzeWithState' substate tbody in
    (state ↖ substate', TWhileLoop { tag=voidType, tcondition=analyzedCondition, tbody=analyzedBody })

analyze' state (TForLoop { tvardecl, tcondition, tincrement, tbody }) =
    let (substate, (analyzedDecl:analyzedCondition:analyzedIncrement:analyzedBody)) = analyzeWithState' (state { scopeLevel=(scopeLevel state) + 1 }) (tvardecl:tcondition:tincrement:tbody) in
    (state ↖ substate,
     TForLoop { tag=voidType, tvardecl=analyzedDecl, tcondition=analyzedCondition, tincrement=analyzedIncrement, tbody=analyzedBody })

analyze' state (TIf { tcondition, ttruebranch, tfalsebranch }) =
    let (substate, analyzedCondition) = analyze' state { scopeLevel=(scopeLevel state) + 1 } tcondition
        (substate', analyzedTrueBranch) = analyze' substate ttruebranch
        (substate'', analyzedFalseBranch) = analyzeFalseBranch (substate ↖ substate') tfalsebranch in
    (state ↖ substate'', TIf { tag=voidType, tcondition=analyzedCondition, ttruebranch=analyzedTrueBranch, tfalsebranch=analyzedFalseBranch })
    where analyzeFalseBranch state Nothing = (state, Nothing)
          analyzeFalseBranch state (Just stmt) = let (substate, analyzedStmt) = analyze' state stmt in
                                                 (substate, Just analyzedStmt)

-- Given two predicates, p and f, returns (Just Term) if (f Term) is
-- True, otherwise recursively searches Term if (p Term) is True, or
-- returns Nothing if both are False.
-- So basically, find1 searches for a Term that satisfies f, but only
-- "enters" a sub-Term if p returns True.
-- Only searches executable code; not declarations.
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
find1 p f t@(TAssign { tavar, tavalue })
    | f t = Just t
    | p t = recsearch (find1 p f) (tavar:tavalue:[])
    | otherwise = Nothing
find1 p f t@(TReturn { tvalue=Just x })
    | f t = Just t
    | p t = find1 p f x
    | otherwise = Nothing
find1 p f t@(TReturn { tvalue=Nothing })
    | f t = Just t
    | otherwise = Nothing
find1 p f t@(TDeref { toperand })
    | f t = Just t
    | p t = find1 p f toperand
    | otherwise = Nothing
find1 p f t@(TAddr { toperand })
    | f t = Just t
    | p t = find1 p f toperand
    | otherwise = Nothing
find1 p f t@(TSubscript { ttarget, tsubscript })
    | f t = Just t
    | p t = recsearch (find1 p f) (ttarget:tsubscript:[])
    | otherwise = Nothing
find1 p f t@(TMemberAccess { ttarget })
    | f t = Just t
    | p t = find1 p f ttarget
    | otherwise = Nothing
find1 p f t@(TStructLiteral { tfieldvalues })
    | f t = Just t
    | p t = recsearch (find1 p f) $ map snd tfieldvalues
    | otherwise = Nothing
find1 p f t@(TWhileLoop { tcondition, tbody })
    | f t = Just t
    | p t = recsearch (find1 p f) (tcondition:tbody)
    | otherwise = Nothing
find1 p f t@(TForLoop { tvardecl, tcondition, tincrement, tbody })
    | f t = Just t
    | p t = recsearch (find1 p f) (tvardecl:tcondition:tincrement:tbody)
    | otherwise = Nothing
find1 p f t@(TIf { tcondition, ttruebranch, tfalsebranch=Nothing })
    | f t = Just t
    | p t = recsearch (find1 p f) (tcondition:ttruebranch:[])
    | otherwise = Nothing
find1 p f t@(TIf { tcondition, ttruebranch, tfalsebranch=Just tfalseb })
    | f t = Just t
    | p t = recsearch (find1 p f) (tcondition:ttruebranch:tfalseb:[])
    | otherwise = Nothing
find1 _ _ _ = Nothing

analyzeToplevel :: [Term ()] -> [TypedTerm]
analyzeToplevel terms = let result = snd (analyzeWithState terms) in
                        case recsearch (find1 (\_ -> False) isExpression) result of
                          Just thing -> error $ "Expressions not allowed at top-level"
                          Nothing -> result
    where isExpression (TDef { }) = False
          isExpression (TStruct { }) = False
          isExpression (TTypedef { }) = False
          isExpression _ = True

analyzeWithState :: [Term ()] -> (AnalyzerState, [TypedTerm])
analyzeWithState terms = analyzeWithState'
                         (AnalyzerState { symbols=defaultSymTable,
                                          scopeLevel=globalScope,
                                          nextTypeID=startUserDefinedTypeIDs })
                         terms

analyzeWithState' :: AnalyzerState -> [Term ()] -> (AnalyzerState, [TypedTerm])
analyzeWithState' = mapAccumL analyze'
