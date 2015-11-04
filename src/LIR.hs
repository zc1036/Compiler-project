
{-# LANGUAGE NamedFieldPuns #-}

module LIR where

import qualified Parser as P
import qualified Analyzer as A
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.List (mapAccumL, intercalate)
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
           | MemberAccess VReg VReg Int Int -- dst, obj, offset, size
           | Move VReg VReg
           | LoadFuncAddr VReg Int
           | LoadInt VReg Integer
           | LoadFloat VReg Float
           | LoadStringPtr VReg String

instance Show Instr where
    show (Call dst funcid regs) = printf "call %s = funcs[%d] (%s)" (show dst) funcid (intercalate ", " $ map show regs)
    show (ICall dst func regs) = printf "icall %s = %s (%s)" (show dst) (show func) (intercalate ", " $ map show regs)
    show (Return Nothing) = printf "ret"
    show (Return (Just reg)) = printf "ret %s" (show reg)
    show (MemberAccess dst obj offset size) = printf "member %s = (%s + %d).%d" (show dst) (show obj) offset size
    show (Move dst src) = printf "move %s = %s" (show dst) (show src)
    show (LoadFuncAddr dst funcid) = printf "lfa %s = funcs[%d]" (show dst) funcid
    show (LoadInt dst int) = printf "lii %s = %d" (show dst) int
    show (LoadFloat dst float) = printf "lif %s = %f" (show dst) float
    show (LoadStringPtr dst str)
         | length str > 10 = printf "lis %s = '%s'..." (show dst) (take 10 str)
         | otherwise = printf "lis %s = '%s'" (show dst) str

type Term = P.Term

type SymbolRegTable = Map.Map String VReg

-- The [VReg] is a list of the registers used in the body for the
-- parameters of this function.
data FuncInstrs = FuncInstrs [VReg] [Instr] -- arg-registers instructions
                  deriving (Show)

type FuncTable = Map.Map Int FuncInstrs

data LIRState = LIRState { cnextVRegID :: Int,
                           cnextFuncID :: Int,
                           csymbols :: SymbolRegTable,
                           clambdas :: FuncTable }

-- The ID of the function that gets called before main
setupLambdaID = 0

defaultCstate = LIRState { cnextVRegID=1,
                           cnextFuncID=setupLambdaID + 1,
                           clambdas=Map.empty,
                           csymbols=Map.fromList [("null", VReg { regsize=A.pointerSize, regid=0, regconst=True })] }

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

astToLIRToplevel :: [A.TypedTerm] -> Program
astToLIRToplevel terms =
    let (finalState, setupCode) = astToLIRToplevel' defaultCstate terms
    in Program { progLambdas=Map.insert setupLambdaID (FuncInstrs [] (concat setupCode)) (clambdas finalState),
                 progSymbols=csymbols finalState }

astToLIRToplevel' :: LIRState -> [A.TypedTerm] -> (LIRState, [[Instr]])
astToLIRToplevel' = mapAccumL astToLIR'
    where astToLIR' acc x = let (state, (_, instrs)) = astToLIR acc x
                            in (state, instrs)

-- Takes a state and a term and returns a new state, a register that
-- holds the value of the expression of the term, and a list of
-- instructions to compute that value, given that the initial state is
-- what was given to this function. If the given term is a definition,
-- then the LIRState is updated with the name if any, and the
-- instructions for calculating the value of the declaration are
-- returned. If the term is a declaration, LIRState is left unchanged,
-- the Maybe VReg is Nothing, and the instruction list is empty.
astToLIR :: LIRState -> A.TypedTerm -> (LIRState, (Maybe VReg, [Instr]))

astToLIR state@(LIRState { csymbols }) (P.TName { P.tsrepr }) =
    case Map.lookup tsrepr csymbols of
      j@(Just _) -> (state, (j, []))
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
    let (newstate, (Just funcreg, funcinstrs):operandsLIR) = mapAccumL (\s -> astToLIR $ state ↖ s) state (tfun:targs)
        (newstate', callreg) = newreg newstate (A.sizeFromType tag) True
    in (state ↖ newstate', (Just callreg,
                            concat $ [funcinstrs,
                                      concat $ map snd operandsLIR,
                                      [ICall callreg funcreg $ map (fromJust . fst) operandsLIR]]))

astToLIR state@(LIRState { csymbols }) (P.TDef { P.vartag, P.tname, P.tvalue=Just val }) =
    let (newstate, (Just valuereg, valueinstrs)) = astToLIR state val
        ((newstate', reg), optionalMoveInstr) =
            -- we only need the MOVE if the register sizes are different or either reg is mutable
            if varsize == regsize valuereg && A.isImmutable vartag && regconst valuereg
            then ((state ↖ newstate, valuereg), [])
            else (newreg (state ↖ newstate) varsize (A.isImmutable vartag), [Move reg valuereg])
    in ((state ↖ newstate') { csymbols=Map.insert tname reg csymbols },
        (Just reg, valueinstrs ++ optionalMoveInstr))
    where varsize = A.sizeFromType vartag

astToLIR state@(LIRState { csymbols }) (P.TDef { P.vartag, P.tname, P.tvalue=Nothing }) =
    let (newstate, reg) = newreg state (A.sizeFromType vartag) (A.isImmutable vartag)
    in (newstate { csymbols=Map.insert tname reg csymbols }, (Just reg, []))

astToLIR state@(LIRState { clambdas, cnextFuncID }) (P.TLambda { P.tag, P.tbody, P.tbindings }) =
    -- note that we don't need to remove non-global bindings from the
    -- symbol table before we analyze the body of the lambda, because
    -- the semantic analyzer already did that and ensured that the
    -- body only references local names or globals, which means that
    -- all names referenced inside the lambda that are not global are
    -- bound inside the lambda and these will overwrite bindings from
    -- the environment.
    let (lambdaState, _) = astToLIRToplevel' state tbindings
        (bodystate, bodyinstrs) = astToLIRToplevel' lambdaState tbody
        (regstate, funcPtrReg) = newreg (state ↖ bodystate) (A.sizeFromType tag) True
        argRegs = map (((LIR.csymbols lambdaState) Map.!) . P.tname) tbindings
    in (regstate { clambdas=Map.insert cnextFuncID (FuncInstrs argRegs $ concat bodyinstrs) clambdas,
                   cnextFuncID=cnextFuncID + 1 },
        (Just funcPtrReg, [LoadFuncAddr funcPtrReg cnextFuncID]))

astToLIR state (P.TReturn { P.tvalue=Just val }) =
    let (newstate, (reg, instrs)) = astToLIR state val
    in (newstate, (Nothing, instrs ++ [Return reg]))

astToLIR state (P.TReturn { P.tvalue=Nothing }) =
    (state, (Nothing, [Return Nothing]))

astToLIR state (P.TStruct { }) = (state, (Nothing, []))

astToLIR _ _ = error "Bug: Unexpected form in astToLIR"
