import IdentityTesting.BinaryInterpreterDispatchHeader
import IdentityTesting.BinaryInterpreterDispatchExecute

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryRationalRegisters BinaryInterpreterArithmetic

def InstructionFinished (pool : BinaryInterpreterPool.Pool) (s : RationalRegisters)
    (i : RationalInstruction) (code history : List Symbol) (f : State) : Prop :=
  Done f ∧ f.selected = i.op ∧ f.io.tape = tape (i.exec s) ∧ CleanIO f.io ∧
  BinaryInterpreterPool.Clean f.pool ∧ f.io.code = code ∧
  f.io.history = (RationalProgramCode.instruction i).reverse ++ history ∧
  ∀ other, other ≠ i.op → f.pool other = pool other

/-- A single machine reads the operation and destination from its code tape,
selects the corresponding physical group, loads both operands, executes, writes
back and cleans the whole selected group. Other groups remain unchanged. -/
theorem binary_instruction (pool : BinaryInterpreterPool.Pool) (hp : BinaryInterpreterPool.Clean pool)
    (s : RationalRegisters) (i : RationalInstruction)
    (hl : i.lhs.slots ≤ s.length) (hr : i.rhs.slots ≤ s.length) (hd : i.dst < s.length)
    (code history : List Symbol) :
    ∃ n,
      let start := initial pool (tape s) (RationalProgramCode.instruction i ++ code) history
      InstructionFinished pool s i code history (advance n start) ∧
      bitSteps n start ≤ 6000*(rationalRegisterEncoding s+s.length+i.lhs.slots+i.rhs.slots+1)+
        100000000*(rationalEncodingLength (i.lhs.read s)+rationalEncodingLength (i.rhs.read s)+1)^3 := by
  let header := RationalProgramCode.word (RationalProgramCode.opBits i.op) ++ RationalProgramCode.address i.dst
  let body := RationalProgramCode.operand i.lhs ++ RationalProgramCode.operand i.rhs ++ code
  let hist := header.reverse ++ history
  let start := initial pool (tape s) (RationalProgramCode.instruction i ++ code) history
  have hstart : initial pool (tape s) (header ++ body) history = start := by
    simp only [start,header,body,RationalProgramCode.instruction,List.append_assoc]
  obtain ⟨nh,hnh,hch,hphase,hselected,hpool,hcursor,hio⟩ := header_run pool (tape s) i.op i.dst body history
  change bitSteps nh (initial pool (tape s) (header ++ body) history) ≤ _ at hch
  change (advance nh (initial pool (tape s) (header ++ body) history)).phase = _ at hphase
  change (advance nh (initial pool (tape s) (header ++ body) history)).selected = _ at hselected
  change (advance nh (initial pool (tape s) (header ++ body) history)).pool = _ at hpool
  change (advance nh (initial pool (tape s) (header ++ body) history)).cursor i.op = _ at hcursor
  change (advance nh (initial pool (tape s) (header ++ body) history)).io =
    {initialIO (tape s) body hist with destination := List.replicate i.dst false} at hio
  rw [hstart] at hch hphase hselected hpool hcursor hio
  let frame := advance nh start
  let entry := BinaryInterpreterOperandExecute.initial (arithmeticStorage i.op) (tape s)
    (List.replicate i.dst false) body hist
  have hview : execView frame i.op = entry := by
    change frame.io.view i.op (frame.pool i.op) (frame.cursor i.op) = entry
    rw [hio,hpool,hcursor,BinaryInterpreterPool.rearm_selected_initial pool i.op hp]
    exact initialIO_destination_view i.op (tape s) body hist (List.replicate i.dst false)
  have hpframe : BinaryInterpreterPool.Clean frame.pool := by
    rw [hpool]
    exact BinaryInterpreterPool.rearm_clean pool i.op hp
  obtain ⟨ne,he,hce⟩ := BinaryInterpreterOperandExecute.binary_operand_execution i.op s i.lhs i.rhs hl hr i.dst hd code hist
  change BinaryInterpreterOperandExecute.Finished (arithmeticStorage i.op) s i.lhs i.rhs i.dst
    (i.op.eval (i.lhs.read s) (i.rhs.read s)) code hist
    (BinaryInterpreterOperandExecute.advance (arithmeticStorage i.op) ne entry) at he
  let ef := BinaryInterpreterOperandExecute.advance (arithmeticStorage i.op) ne entry
  rcases he with ⟨hel,heh,het,hei,hecore,hetmp,hecode,hehist⟩
  have htotal : advance (nh+ne) start = execLift frame i.op ef := by
    rw [advance_add,running_advance frame i.op hphase hselected ne,hview]
  refine ⟨nh+ne,?_,?_⟩
  · change InstructionFinished pool s i code history (advance (nh+ne) start)
    rw [htotal]
    refine ⟨⟨rfl,hel,heh⟩,rfl,?_,cleanIO_ofExec ef hetmp hei,
      execLift_pool_clean frame i.op ef hpframe hecore,hecode,?_,?_⟩
    · change ef.execution.core.tape = tape (i.exec s)
      exact het
    · change ef.history = (RationalProgramCode.instruction i).reverse ++ history
      rw [hehist]
      simp only [hist,header,RationalProgramCode.instruction,List.reverse_append,List.append_assoc]
    · intro other ho
      rw [execLift_inactive frame i.op other ef ho,hpool]
      exact BinaryInterpreterPool.other_set pool i.op other _ ho
  · change bitSteps (nh+ne) start ≤ _
    rw [bitSteps_add,running_bitSteps frame i.op hphase hselected ne,hview]
    change BinaryInterpreterOperandExecute.bitSteps (arithmeticStorage i.op) ne entry ≤ _ at hce
    omega

/-- The public entry starts from the fixed empty pool; it does not take an
operation, destination, or local execution certificate as machine input. -/
theorem binary_instruction_from_empty (s : RationalRegisters) (i : RationalInstruction)
    (hl : i.lhs.slots ≤ s.length) (hr : i.rhs.slots ≤ s.length) (hd : i.dst < s.length)
    (code history : List Symbol) :
    ∃ n,
      let start := initial BinaryInterpreterPool.empty (tape s) (RationalProgramCode.instruction i ++ code) history
      InstructionFinished BinaryInterpreterPool.empty s i code history (advance n start) ∧
      bitSteps n start ≤ 6000*(rationalRegisterEncoding s+s.length+i.lhs.slots+i.rhs.slots+1)+
        100000000*(rationalEncodingLength (i.lhs.read s)+rationalEncodingLength (i.rhs.read s)+1)^3 :=
  binary_instruction BinaryInterpreterPool.empty BinaryInterpreterPool.empty_clean s i hl hr hd code history

end IdentityTesting.BinaryInterpreterDispatch
