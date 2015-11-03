
{-# LANGUAGE NamedFieldPuns #-}

module LIR where

import qualified Parser as P
import qualified Analyzer as A
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.List (foldl, mapAccumL)
import Text.Printf

data VReg = VReg { regsize :: Integer, regid :: Int, regconst :: Bool }

instance Show Vreg where
    show (VReg { regsize, regid, regconst })
         | regconst = "$" ++ (show regid) ++ "c." ++ (show regsize)
         | otherwise = "$" ++ (show regid) ++ "." ++ (show regsize)

-- Instructions Take the form:
-- -  Operator destination [operand-1, [operand-2, ...]]
-- -  Operator operand
data Instr = Call VReg Int [VReg] -- dst, func id, [args]
           | ICall VReg VReg [VReg] -- dst, func address, [args]
           | Return VReg
           | MemberAccess VReg VReg Int Int -- dst, obj, offset, size
           | Move VReg VReg
           | LoadFuncAddr VReg Int
           | LoadInt VReg Integer
           | LoadFloat VReg Float
           | LoadStringPtr VReg String

instance Show Instr where
    show (Call dst funcid regs) = printf "call %s = funcs[%d] (%s)" (show dst) funcid (intercalate ", " $ map show regs)
    show (ICall dst func regs) = printf "icall %s = %s (%s)" (show dst) (show func) (intercalate ", " $ map show args)
    show (Return reg) = printf "ret %s" (show reg)
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
type FuncTable = Map.Map Int [Instr]

data LIRState = LIRState { cnextVRegID :: Int,
                           cnextFuncID :: Int,
                           csymbols :: SymbolRegTable,
                           clambdas :: FuncTable,
                           cscopeLevel :: Int }

-- The ID of the function that gets called before main
setupLambdaID=0

defaultCstate :: LIRState
defaultCstate = LIRState { cnextVRegID=1,
                           cnextFuncID=setupLambdaID + 1,
                           clambdas=Map.empty,
                           csymbols=Map.empty,
                           cscopeLevel=A.globalScope }

passup :: LIRState -> LIRState -> LIRState
passup state newstate = state { cnextVRegID=(cnextVRegID newstate),
                                cnextFuncID=(cnextFuncID newstate) }

data Program = Program { progLambdas :: FuncTable, progSymbols :: SymbolRegTable }

-- Helper function to create a new vreg and update the state
newreg :: LIRState -> Integer -> Bool -> (LIRState, VReg)
newreg state@(LIRState { cnextVRegID }) size const = (state { cnextVRegID=cnextVRegID + 1 },
                                                      VReg { regsize=size, regid=cnextVRegID, regconst=const })

astToLIRToplevel :: [A.TypedTerm] -> Program
astToLIRToplevel terms =
    let (finalState, setupCode) = astToLIRToplevel' defaultCstate terms in
    Program { progLambdas=Map.insert setupLambdaID (concat . reverse $ setupCode) (clambdas finalState),
              progSymbols=csymbols finalState }

astToLIRToplevel' :: LIRState -> [A.TypedTerm] -> (LIRState, [[Instr]])
astToLIRToplevel' = mapAccumL astToLIR'
    where astToLIR' acc x = let (state, (_, instrs)) = astToLIR acc x in (state, instrs)

-- Takes a state and a term and returns a new state, a register that
-- holds the value of the expression of the term, and a list of
-- instructions to compute that value, given that the initial state is
-- what was given to this function. If the given term is a definition,
-- then the LIRState is updated with the name if any, and the
-- instructions for calculating the value of the declaration are
-- returned. If the term is a declaration, LIRState is left unchanged,
-- the Maybe VReg is Nothing, and the instruction list is empty.
astToLIR :: LIRState -> A.TypedTerm -> (LIRState, (Maybe VReg, [Instr]))

astToLIR state@(LIRState { cnextVRegID, csymbols }) (P.TName { P.tag, P.tsrepr }) =
    case Map.lookup tsrepr csymbols of
      j@(Just reg) -> (state, (j, []))
      Nothing -> error $ "Bug: Somehow the symbol " ++ tsrepr ++ " was not assigned a vreg"

astToLIR state (P.TIntLiteral { P.tirepr }) =
    let (newstate, reg) = newreg state A.intSize True in
    (newstate, (Just reg, [LoadInt reg tirepr]))

astToLIR state (P.TFloatLiteral { P.tfrepr }) =
    let (newstate, reg) = newreg state A.floatSize True in
    (newstate, (Just reg, [LoadFloat reg tfrepr]))

astToLIR state (P.TStringLiteral { P.tsrepr }) =
    let (newstate, reg) = newreg state A.pointerSize True in
    (newstate, (Just reg, [LoadStringPtr reg tsrepr]))

astToLIR state (P.TFuncall { P.tag, P.tfun, P.targs }) =
    let (newstate, (Just funcreg, funcinstrs):operandsLIR) = mapAccumL (\s -> astToLIR $ passup state s) state (tfun:targs)
        (newstate', callreg) = newreg newstate (A.sizeFromType tag) True in
    (passup state newstate', (Just callreg,
                              concat $ [funcinstrs,
                                        concat $ map snd operandsLIR,
                                        [ICall callreg funcreg $ map (fromJust . fst) operandsLIR]]))

astToLIR state (P.TDef { tag, tname, tvalue }) =
    let (newstate, (Just valuereg, valueinstrs)) = 

-- let reg = VReg { regsize=A.sizeFromType tag, regid=cnextVRegID, regconst=not $ A.isMutable tag } in
--                  (state { cnextVRegID=cnextVRegID + 1, csymbols=Map.insert tsrepr reg csymbols }, Just reg, [])

astToLIR state (P.TStruct { }) = (state, (Nothing, []))

astToLIR _ _ = error "Bug: Unexpected form in astToLIR"
