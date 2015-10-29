
{-# LANGUAGE NamedFieldPuns #-}

module LIR where

import qualified Parser as P
import qualified Analyzer as A
import Data.Maybe
import qualified Data.Map.Strict as Map
import Data.List (foldl)

data VReg = VReg { regsize :: Int, regid :: Int, regconst :: Bool }
            deriving (Show)

-- Instructions Take the form:
-- -  Operator destination [operand-1, [operand-2, ...]]
-- -  Operator operand
data Instr = Call VReg Int [VReg] -- dst, func id, [args]
           | ICall VReg VReg [VReg] -- dst, func address, [args]
           | Return VReg
           | LoadFuncAddr VReg Int
           | MemberAccess VReg VReg Int Int -- dst, obj, offset, size
           | Move VReg VReg
             deriving (Show)

type Term = P.Term

type SymbolRegTable = Map.Map String VReg
type FuncTable = Map.Map Int [Instr]

data CState = CState { cnextVRegID :: Int,
                       cnextFuncID :: Int,
                       csymbols :: SymbolRegTable,
                       clambdas :: FuncTable,
                       cscopeLevel :: Int }

-- The ID of the function that gets called before main
setupLambdaID=0

defaultCstate :: CState
defaultCstate = CState { cnextVRegID=1,
                         cnextFuncID=setupLambdaID + 1,
                         clambdas=Map.empty,
                         csymbols=Map.empty,
                         cscopeLevel=A.globalScope }

passup :: CState -> CState -> CState

data Program = Program { progLambdas :: FuncTable, progSymbols :: SymbolRegTable }

astToLIRToplevel :: [A.TypedTerm] -> IRProgram
astToLIRToplevel terms = let (finalState, setupCode) = foldl astToLIRToplevel' (defaultCstate, []) terms in
                         Program { progLambdas=Map.insert setupLambdaID (concat . reverse $ setupCode) (clambdas finalState),
                                   progSymbols=csymbols finalState }
    where astToLIRToplevel' (initState, setupCode) s@(TStruct { }) = (initState, setupCode)
          astToLIRToplevel' (initState, setupCode) t = let (newstate, _, instrs) = astToLIR initState def in
                                                       (newstate, (instrs:setupCode))

-- Takes a state and a term and returns a new state, a register that
-- holds the value of the expression of the term, and a list of
-- instructions to compute that value, given that the initial state is
-- what was given to this function. If the given term is a definition,
-- then the LIRState is updated with the name if any, and the
-- instructions for calculating the value of the declaration are
-- returned. If the term is a declaration, LIRState is left unchanged,
-- the Maybe VReg is Nothing, and the instruction list is empty.
astToLIR :: LIRState -> A.TypedTerm -> (LIRState, Maybe VReg, [Instr])
astToLIR state 
