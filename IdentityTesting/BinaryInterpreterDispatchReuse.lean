import IdentityTesting.BinaryInterpreterDispatchRuns

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic

/-- Reset only the finite control. Physical pool stacks and all shared I/O
lists are retained. This is an interface for a subsequent program dispatcher. -/
def rearmIO (io : IO) : IO :=
  {io with
    negative := false
    loading := true
    executionPhase := .running
    arithmeticPhase := .operating
    pairPhase := .left
    operandPhase := .kind
    literalPhase := .sign
    fieldPhase := .reading
    readPhase := .reading
    seekPhase := .seek
    splitPhase := .sign
    storePhase := .joining
    joinPhase := .denCollect
    writePhase := .seek}

def rearm (s : State) : State :=
  {s with
    phase := .tag
    tagPhase := .first
    first := false
    second := false
    third := false
    selected := .copy
    cursor := fun op => ⟨(arithmeticStorage op).count,by omega⟩
    io := rearmIO s.io}

theorem rearm_preserves (s : State) :
    (rearm s).pool = s.pool ∧ (rearm s).io.tape = s.io.tape ∧
    (rearm s).io.code = s.io.code ∧ (rearm s).io.history = s.io.history ∧
    (rearm s).io.temp = s.io.temp ∧ (rearm s).io.leftAddress = s.io.leftAddress ∧
    (rearm s).io.rightAddress = s.io.rightAddress ∧ (rearm s).io.destination = s.io.destination ∧
    (rearm s).io.saved = s.io.saved ∧ (rearm s).io.copyTemp = s.io.copyTemp ∧
    (rearm s).io.record = s.io.record ∧ (rearm s).io.numWork = s.io.numWork ∧
    (rearm s).io.denWork = s.io.denWork := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem rearm_clean (s : State) (h : CleanIO s.io) :
    rearm s = initial s.pool s.io.tape s.io.code s.io.history := by
  rcases h with ⟨ht,hl,hr,hd,hs,hc,hrec,hn,hden⟩
  cases s
  simp_all [rearm,rearmIO,initial,initialIO,IO.ofExec,BinaryInterpreterOperandExecute.initial,
    BinaryInterpreterArithmeticClean.runningState,BinaryInterpreterArithmetic.operatingState]

/-- Reuse starts from the same physical pool and the unread code suffix.
No new program-level iteration or rewind theorem is asserted here. -/
theorem instruction_from_rearmed (s : State) (hio : CleanIO s.io)
    (hp : BinaryInterpreterPool.Clean s.pool) (regs : RationalRegisters) (i : RationalInstruction)
    (ht : s.io.tape = BinaryRationalRegisters.tape regs)
    (code : List Symbol) (hc : s.io.code = RationalProgramCode.instruction i ++ code)
    (hl : i.lhs.slots ≤ regs.length) (hr : i.rhs.slots ≤ regs.length) (hd : i.dst < regs.length) :
    ∃ n, InstructionFinished s.pool regs i code s.io.history (advance n (rearm s)) ∧
      bitSteps n (rearm s) ≤ 6000*(rationalRegisterEncoding regs+regs.length+i.lhs.slots+i.rhs.slots+1)+
        100000000*(rationalEncodingLength (i.lhs.read regs)+rationalEncodingLength (i.rhs.read regs)+1)^3 := by
  rw [rearm_clean s hio,ht,hc]
  exact binary_instruction s.pool hp regs i hl hr hd code s.io.history

end IdentityTesting.BinaryInterpreterDispatch
