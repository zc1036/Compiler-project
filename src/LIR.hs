
{-# LANGUAGE NamedFieldPuns #-}

module LIR where

import qualified Parser as P
import qualified Analyzer as A
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.List (mapAccumL, intercalate, findIndex)
import Text.Printf
import Debug.Trace

data VReg = VReg { regsize :: Integer, regid :: Int, regconst :: Bool }

instance Show VReg where
    show (VReg { regsize, regid, regconst })
         | regconst = "$" ++ (show regid) ++ "c." ++ (show regsize)
         | otherwise = "$" ++ (show regid) ++ "." ++ (show regsize)

-- Instructions Take the form:
-- -  Operator destination [operand-1, [operand-2, ...]]
-- -  Operator operand
data Instr = Call VReg Int [VReg] -- dst, func id, [args]
           | ICall VReg VReg [VReg] -- dst, func address, [args]
           | Return (Maybe VReg)
           | Move VReg VReg
           | Store VReg VReg
           | StoreArray VReg VReg VReg -- v1[v2] = v3
           | LoadArray VReg VReg VReg --  v1 = v2[v3]
           | Load VReg VReg
           | LoadAddressOf VReg VReg
           | LoadFuncAddr VReg Int
           | LoadInt VReg Integer
           | LoadFloat VReg Float
           | LoadStringPtr VReg String
           | LoadStructMember VReg VReg Int -- dst src offset (size of load is in the dst register)
           | Add VReg VReg VReg
           | Mult VReg VReg VReg

instance Show Instr where
    show (Call dst funcid regs) = printf "call %s = funcs[%d] (%s)" (show dst) funcid (intercalate ", " $ map show regs)
    show (ICall dst func regs) = printf "icall %s = %s (%s)" (show dst) (show func) (intercalate ", " $ map show regs)
    show (Return Nothing) = printf "ret"
    show (Return (Just reg)) = printf "ret %s" (show reg)
    show (Move dst src) = printf "move %s = %s" (show dst) (show src)
    show (Load dst src) = printf "load %s = %s" (show dst) (show src)
    show (Store dst src) = printf "store %s = %s" (show dst) (show src)
    show (LoadArray dst arr offset) = printf "loada %s = %s[%s]" (show dst) (show arr) (show offset)
    show (StoreArray arr offset val) = printf "storea %s[%s] = %s" (show arr) (show offset) (show val)
    show (LoadAddressOf dst obj) = printf "lao %s = & %s" (show dst) (show obj)
    show (LoadStructMember dst obj offset) = printf "member %s = (%s[%d..$d])" (show dst) (show obj) offset (regsize dst)
    show (Add dst op1 op2) = printf "add %s = %s + %s" (show dst) (show op1) (show op2)
    show (Mult dst op1 op2) = printf "mult %s = %s * %s" (show dst) (show op1) (show op2)
    show (LoadFuncAddr dst funcid) = printf "lfa %s = funcs[%d]" (show dst) funcid
    show (LoadInt dst int) = printf "lii %s = %d" (show dst) int
    show (LoadFloat dst float) = printf "lif %s = %f" (show dst) float
    show (LoadStringPtr dst str)
         | length str > 10 = printf "lis %s = '%s'..." (show dst) (take 10 str)
         | otherwise = printf "lis %s = '%s'" (show dst) str

type Term = P.Term

type SymbolRegTable = Map.Map String (Int, VReg)

-- The [VReg] is a list of the registers used in the body for the
-- parameters of this function.
data FuncInstrs = FuncInstrs [VReg] [Instr] -- arg-registers instructions
                  deriving (Show)

type FuncTable = Map.Map Int FuncInstrs

data LIRState = LIRState { cnextVRegID :: Int,
                           cnextFuncID :: Int,
                           csymbols :: SymbolRegTable,
                           clambdas :: FuncTable,
                           scopeLevel :: Int }

-- The ID of the function that gets called before main
setupLambdaID :: Int
setupLambdaID = 0

globalScope :: Int
globalScope = 0

defaultCstate = LIRState { cnextVRegID=1,
                           cnextFuncID=setupLambdaID + 1,
                           clambdas=Map.empty,
                           csymbols=Map.fromList [("null", (globalScope, VReg { regsize=A.pointerSize, regid=0, regconst=True }))],
                           scopeLevel=globalScope }

(↖) :: LIRState -> LIRState -> LIRState
state ↖ newstate = state { cnextVRegID=cnextVRegID newstate,
                           cnextFuncID=cnextFuncID newstate,
                           clambdas=clambdas newstate }

data Program = Program { progLambdas :: FuncTable, progSymbols :: SymbolRegTable }
               deriving (Show)

-- Helper function to create a new vreg and update the state
newreg :: LIRState -> Integer -> Bool -> (LIRState, VReg)
newreg state@(LIRState { cnextVRegID }) size const = (state { cnextVRegID=cnextVRegID + 1 },
                                                      VReg { regsize=size, regid=cnextVRegID, regconst=const })

newregs :: LIRState -> [(Integer, Bool)] -> (LIRState, [VReg])
newregs = mapAccumL (\st (sz, cnst) -> newreg st sz cnst)

astToLIRToplevel :: [A.TypedTerm] -> Program
astToLIRToplevel terms =
    let (finalState, setupCode) = astToLIRToplevel' defaultCstate terms
    in Program { progLambdas=Map.insert setupLambdaID (FuncInstrs [] (concat setupCode)) (clambdas finalState),
                 progSymbols=csymbols finalState }

astToLIRToplevel' :: LIRState -> [A.TypedTerm] -> (LIRState, [[Instr]])
astToLIRToplevel' = mapAccumL astToLIR'
    where astToLIR' acc x = let (state, (_, instrs)) = astToLIR acc x
                            in (state, instrs)

-- Takes a state, boolean if at global scope, and a term and returns a
-- new state, a register that holds the value of the expression of the
-- term, and a list of instructions to compute that value, given that
-- the initial state is what was given to this function. If the given
-- term is a definition, then the LIRState is updated with the name if
-- any, and the instructions for calculating the value of the
-- declaration are returned. If the term is a declaration, LIRState is
-- left unchanged, the Maybe VReg is Nothing, and the instruction list
-- is empty.
astToLIR :: LIRState -> A.TypedTerm -> (LIRState, (Maybe VReg, [Instr]))

astToLIR state@(LIRState { csymbols }) (P.TName { P.tsrepr }) =
    case Map.lookup tsrepr csymbols of
      Just (_, reg) -> (state, (Just reg, []))
      Nothing -> error $ "Bug: Somehow the symbol " ++ tsrepr ++ " was not assigned a vreg"

astToLIR state (P.TIntLiteral { P.tirepr }) =
    let (newstate, reg) = newreg state A.intSize True
    in (newstate, (Just reg, [LoadInt reg tirepr]))

astToLIR state (P.TFloatLiteral { P.tfrepr }) =
    let (newstate, reg) = newreg state A.floatSize True
    in (newstate, (Just reg, [LoadFloat reg tfrepr]))

astToLIR state (P.TStringLiteral { P.tsrepr }) =
    let (newstate, reg) = newreg state A.pointerSize True
    in (newstate, (Just reg, [LoadStringPtr reg tsrepr]))

astToLIR state (P.TFuncall { P.tag, P.tfun, P.targs }) =
    let (newstate, (Just funcreg, funcinstrs):operandsLIR) = mapAccumL (astToLIR . (state ↖)) state (tfun:targs)
        (newstate', callreg) = newreg newstate (A.sizeFromType tag) True
    in (state ↖ newstate', (Just callreg,
                            concat $ [funcinstrs,
                                      concat $ map snd operandsLIR,
                                      [ICall callreg funcreg $ map (fromJust . fst) operandsLIR]]))

astToLIR state@(LIRState { csymbols, scopeLevel }) (P.TDef { P.vartag, P.tname, P.tvalue=Just val }) =
    let (newstate, (Just valuereg, valueinstrs)) = astToLIR state val
        ((newstate', reg), optionalMoveInstr) =
            -- we only need the MOVE if the register sizes are different or either reg is mutable
            if varsize == regsize valuereg && A.isImmutable vartag && regconst valuereg
            then ((state ↖ newstate, valuereg), [])
            else (newreg (state ↖ newstate) varsize (A.isImmutable vartag), [Move reg valuereg])
    in ((state ↖ newstate') { csymbols=Map.insert tname (scopeLevel, reg) csymbols },
        (Just reg, valueinstrs ++ optionalMoveInstr))
    where varsize = A.sizeFromType vartag

astToLIR state@(LIRState { csymbols, scopeLevel }) (P.TDef { P.vartag, P.tname, P.tvalue=Nothing }) =
    let (newstate, reg) = newreg state (A.sizeFromType vartag) (A.isImmutable vartag)
    in (newstate { csymbols=Map.insert tname (scopeLevel, reg) csymbols }, (Just reg, []))

astToLIR state@(LIRState { clambdas, cnextFuncID, csymbols, scopeLevel }) (P.TLambda { P.tag, P.tbody, P.tbindings }) =
    let (lambdaState, _) = astToLIRToplevel' state tbindings
        (bodystate, bodyinstrs) = astToLIRToplevel' (lambdaState { csymbols=symbolTableWithoutLocalValues,
                                                                   scopeLevel=scopeLevel + 1 }) tbody
        (regstate, funcPtrReg) = newreg (state ↖ bodystate) (A.sizeFromType tag) True
        argRegs = map (snd . ((LIR.csymbols lambdaState) Map.!) . P.tname) tbindings
    in (regstate { clambdas=Map.insert cnextFuncID (FuncInstrs argRegs $ concat bodyinstrs) clambdas,
                   cnextFuncID=cnextFuncID + 1 },
        (Just funcPtrReg, [LoadFuncAddr funcPtrReg cnextFuncID]))
    where filterSymbolTable (scope, _) = scope == globalScope
          symbolTableWithoutLocalValues = Map.filter filterSymbolTable csymbols
      
astToLIR state (P.TAssign { P.tavar=n@(P.TName { P.tsrepr }), P.tavalue }) =
    let (_, (Just namereg, [])) = astToLIR state n
        (newstate, (Just valreg, valinstrs)) = astToLIR state tavalue
    in (state ↖ newstate, (Just namereg, valinstrs ++ [Move namereg valreg]))

astToLIR state (P.TAssign { P.tavar=(P.TDeref { P.toperand }), P.tavalue }) =
    let (newstate, (Just opreg, opinstrs)) = astToLIR state toperand
        (newstate', (Just valreg, valinstrs)) = astToLIR (state ↖ newstate) tavalue
    in (state ↖ newstate', (Nothing, opinstrs ++ valinstrs ++ [Store opreg valreg]))

astToLIR state (P.TAssign { P.tavar=(P.TSubscript { P.ttarget, P.tsubscript }), P.tavalue }) =
    let (newstate, (Just targetreg, targetinstrs)) = astToLIR state ttarget
        (newstate', (Just subreg, subinstrs)) = astToLIR (state ↖ newstate) tsubscript
        (newstate'', (Just valreg, valinstrs)) = astToLIR (state ↖ newstate') tavalue
        (finalState, storeinstrs) = makeStore (state ↖ newstate'') (P.tag ttarget) targetreg subreg valreg
    in (finalState, (Nothing, targetinstrs ++ subinstrs ++ valinstrs ++ storeinstrs))
    where makeStore state (A.Mutable t) targetreg subreg valreg = makeStore state t targetreg subreg valreg
          makeStore state (A.Array _ t) targetreg subreg valreg =
              let (newstate, [szreg, offsetreg]) = newregs state [(A.pointerSize, True),
                                                                  (A.pointerSize, True)]
              in (newstate, [LoadInt szreg (A.sizeFromType t),
                             Mult offsetreg szreg subreg,
                             StoreArray targetreg offsetreg valreg])
          makeStore state (A.Ptr t) targetreg subreg valreg =
              let (newstate, [szreg, offsetreg, addrreg]) = newregs state [(A.pointerSize, True),
                                                                           (A.pointerSize, True),
                                                                           (A.pointerSize, True)]
              in (newstate, [LoadInt szreg (A.sizeFromType t),
                             Mult offsetreg szreg subreg,
                             Add addrreg offsetreg targetreg,
                             Store addrreg valreg])
          makeStore _ x _ _ _ = error $ "Unexpected type in assignment to subscript: " ++ (show x)

astToLIR state (P.TReturn { P.tvalue=Just val }) =
    let (newstate, (reg, instrs)) = astToLIR state val
    in (state ↖ newstate, (Nothing, instrs ++ [Return reg]))

astToLIR state (P.TDeref { P.tag, P.toperand }) =
    let (newstate, (Just opreg, instrs)) = astToLIR state toperand
        (newstate', valreg) = newreg (state ↖ newstate) (A.sizeFromType tag) (A.isImmutable tag)
    in (state ↖ newstate', (Just valreg, instrs ++ [Load valreg opreg]))

astToLIR state (P.TSubscript { P.tag, P.ttarget, P.tsubscript }) =
    let (newstate, (Just targetreg, targetinstrs)) = astToLIR state ttarget
        (newstate', (Just subreg, subinstrs)) = astToLIR (state ↖ newstate) tsubscript
        (newstate'', outreg) = newreg (state ↖ newstate') (A.sizeFromType tag) (A.isImmutable tag)
        (finalState, loadinstrs) = makeLoad (state ↖ newstate'') (P.tag ttarget) outreg targetreg subreg
    in (finalState, (Just outreg, targetinstrs ++ subinstrs ++ loadinstrs))
    where makeLoad state (A.Mutable x) outreg targetreg subreg = makeLoad state x outreg targetreg subreg
          makeLoad state (A.Ptr t) outreg targetreg subreg = let (newstate, [szreg, offsetreg, addrreg])
                                                                     = newregs state [(A.pointerSize, True),
                                                                                      (A.pointerSize, True),
                                                                                      (A.pointerSize, True)]
                                                             in (newstate, [LoadInt szreg (A.sizeFromType t),
                                                                            Mult offsetreg szreg subreg,
                                                                            Add addrreg targetreg offsetreg,
                                                                            Load outreg addrreg])
          makeLoad state (A.Array _ t) outreg targetreg subreg = let (newstate, [szreg, offsetreg])
                                                                         = newregs state [(A.pointerSize, True),
                                                                                          (A.pointerSize, True)]
                                                                 in (newstate, [LoadInt szreg (A.sizeFromType t),
                                                                                Mult offsetreg szreg subreg,
                                                                                LoadArray outreg targetreg offsetreg])
          makeLoad _ t _ _ _ = error $ "Unexpected type in load from subscript: " ++ (show t)

astToLIR state (P.TAddr { P.toperand }) =
    let (newstate, (Just opreg, instrs)) = astToLIR state toperand
        (newstate', dstreg) = newreg newstate A.pointerSize True
    in (state ↖ newstate', (Just dstreg, instrs ++ [LoadAddressOf dstreg opreg]))

astToLIR state (P.TMemberAccess { P.ttarget, P.tmember, P.tag }) =
    let (newstate, (Just opreg, opinstrs)) = astToLIR state ttarget
        (newstate', dstreg) = newreg (state ↖ newstate) (A.sizeFromType tag) (A.isImmutable tag)
    in (state ↖ newstate', (Just dstreg, opinstrs ++ [LoadStructMember dstreg opreg $ memberOffset (P.tag ttarget)]))
    where memberOffset (A.Mutable x) = memberOffset x
          memberOffset (A.Unqualified (A.Struct { A.fields, A.fieldOffsets })) =
              fromIntegral $ fieldOffsets !! (fromJust $ findIndex (\x -> fst x == tmember) fields)

astToLIR state (P.TReturn { P.tvalue=Nothing }) =
    (state, (Nothing, [Return Nothing]))

astToLIR state (P.TStruct { }) = (state, (Nothing, []))

astToLIR _ _ = error "Bug: Unexpected form in astToLIR"
