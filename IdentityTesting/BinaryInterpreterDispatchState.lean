import IdentityTesting.BinaryInterpreterOperandExecuteInstances
import IdentityTesting.BinaryInterpreterPool

/-! One shared I/O workspace and a fixed six-operation pool. A selected core is
a view into the pool, not a freshly allocated copy. All cursor fields have fixed
finite types; no unbounded host counter is used for dispatch. -/
namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic

structure IO where
  tape : List Symbol
  code : List Symbol
  history : List Symbol
  temp : List Bool
  leftAddress : List Bool
  rightAddress : List Bool
  destination : List Bool
  saved : List Symbol
  copyTemp : List Cell
  record : List Cell
  numWork : List Bool
  denWork : List Bool
  negative : Bool
  loading : Bool
  executionPhase : BinaryInterpreterArithmeticClean.Phase
  arithmeticPhase : BinaryInterpreterArithmetic.Phase
  pairPhase : BinaryInterpreterOperandPair.Phase
  operandPhase : BinaryInterpreterOperand.Phase
  literalPhase : BinaryCodeLiteralLoader.Phase
  fieldPhase : BinaryCodeWordLoader.Phase
  readPhase : BinaryInterpreterRead.Phase
  seekPhase : BinaryRegisterMachine.Phase
  splitPhase : BinaryRationalRecordMachine.Phase
  storePhase : BinaryInterpreterWrite.Phase
  joinPhase : BinaryRationalRecordJoin.Phase
  writePhase : BinaryRegisterWriteMachine.Phase

def IO.ofExec {op : RationalOp} (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) : IO :=
  ⟨e.execution.core.tape, e.code, e.history, e.temp,
    e.execution.core.leftAddress, e.execution.core.rightAddress, e.execution.core.destination,
    e.execution.core.saved, e.execution.core.copyTemp, e.execution.core.record,
    e.execution.core.numWork, e.execution.core.denWork, e.execution.core.negative,
    e.loading, e.execution.phase, e.execution.core.phase, e.pairPhase, e.operandPhase,
    e.literalPhase, e.fieldPhase, e.execution.core.readPhase, e.execution.core.seekPhase,
    e.execution.core.splitPhase, e.execution.core.storePhase, e.execution.core.joinPhase,
    e.execution.core.writePhase⟩

def IO.view (io : IO) (op : RationalOp) (c : (arithmeticLayout op).Core)
    (cursor : Fin ((arithmeticStorage op).count+1)) :
    BinaryInterpreterOperandExecute.State (arithmeticStorage op) :=
  ⟨io.loading, ⟨io.executionPhase,
    ⟨io.arithmeticPhase,c,io.tape,io.leftAddress,io.rightAddress,io.destination,
      io.saved,io.copyTemp,io.record,io.numWork,io.denWork,io.negative,
      io.readPhase,io.seekPhase,io.splitPhase,io.storePhase,io.joinPhase,io.writePhase⟩,cursor⟩,
    io.pairPhase,io.operandPhase,io.literalPhase,io.fieldPhase,io.code,io.history,io.temp⟩

theorem IO.of_view (io : IO) (op : RationalOp) (c : (arithmeticLayout op).Core)
    (cursor : Fin ((arithmeticStorage op).count+1)) : IO.ofExec (io.view op c cursor) = io := rfl
theorem IO.view_of {op : RationalOp} (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    (IO.ofExec e).view op e.execution.core.core e.execution.cursor = e := rfl

inductive Phase where
  | tag | address | running | invalid
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  tagPhase : BinaryCodeTagDecoder.Phase
  first : Bool
  second : Bool
  third : Bool
  selected : RationalOp
  pool : BinaryInterpreterPool.Pool
  cursor : (op : RationalOp) → Fin ((arithmeticStorage op).count+1)
  io : IO

def execView (s : State) (op : RationalOp) : BinaryInterpreterOperandExecute.State (arithmeticStorage op) :=
  s.io.view op (s.pool op) (s.cursor op)
def setExec (s : State) (op : RationalOp) (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) : State :=
  {s with
    pool := BinaryInterpreterPool.set s.pool op e.execution.core.core
    cursor := Function.update s.cursor op e.execution.cursor
    io := IO.ofExec e}

theorem execView_set (s : State) (op : RationalOp) (e : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    execView (setExec s op e) op = e := by
  simp [execView,setExec,BinaryInterpreterPool.get_set,IO.view_of]
theorem setExec_set (s : State) (op : RationalOp)
    (e f : BinaryInterpreterOperandExecute.State (arithmeticStorage op)) :
    setExec (setExec s op e) op f = setExec s op f := by
  simp [setExec,BinaryInterpreterPool.set_set]
theorem setExec_view (s : State) (op : RationalOp) : setExec s op (execView s op) = s := by
  simp [setExec,execView,IO.view,BinaryInterpreterPool.set_self,IO.ofExec]

def initialIO (tape code history : List Symbol) : IO :=
  IO.ofExec (BinaryInterpreterOperandExecute.initial (arithmeticStorage .copy) tape [] code history)

def initial (pool : BinaryInterpreterPool.Pool) (tape code history : List Symbol) : State :=
  ⟨.tag,.first,false,false,false,.copy,pool,fun op => ⟨(arithmeticStorage op).count,by omega⟩,
    initialIO tape code history⟩

theorem initialIO_view (op : RationalOp) (tape code history : List Symbol) :
    (initialIO tape code history).view op
      ((arithmeticLayout op).initial emptyWord emptyWord) ⟨(arithmeticStorage op).count,by omega⟩ =
      BinaryInterpreterOperandExecute.initial (arithmeticStorage op) tape [] code history := rfl

end IdentityTesting.BinaryInterpreterDispatch
