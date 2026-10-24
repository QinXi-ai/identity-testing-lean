import IdentityTesting.BinaryInterpreterOperandPairRuns
import IdentityTesting.BinaryInterpreterArithmeticCleanBound

/-! Operand-code loading and arithmetic execution share one core and one set
of register-I/O stacks. The dispatch changes finite control only. The operation
and destination are supplied externally here; instruction decoding is separate. -/
namespace IdentityTesting.BinaryInterpreterOperandExecute
open BinaryInterpreterLayout BinaryInterpreterStorage BinaryRegisterMachine
variable {L : Layout} (W : Storage L)

structure State where
  loading : Bool
  execution : BinaryInterpreterArithmeticClean.State W
  pairPhase : BinaryInterpreterOperandPair.Phase
  operandPhase : BinaryInterpreterOperand.Phase
  literalPhase : BinaryCodeLiteralLoader.Phase
  fieldPhase : BinaryCodeWordLoader.Phase
  code : List Symbol
  history : List Symbol
  temp : List Bool

def pairView (s : State W) : BinaryInterpreterOperandPair.State L :=
  ⟨s.pairPhase, ⟨s.operandPhase,
    ⟨s.execution.core.core, s.literalPhase, s.fieldPhase, s.code, s.history, s.temp⟩,
    s.execution.core.tape, s.execution.core.leftAddress, s.execution.core.saved,
    s.execution.core.copyTemp, s.execution.core.record, s.execution.core.numWork,
    s.execution.core.denWork, s.execution.core.readPhase, s.execution.core.seekPhase,
    s.execution.core.splitPhase⟩⟩

def setPair (s : State W) (p : BinaryInterpreterOperandPair.State L) : State W :=
  {s with
    pairPhase := p.phase
    operandPhase := p.loader.phase
    literalPhase := p.loader.data.phase
    fieldPhase := p.loader.data.fieldPhase
    code := p.loader.data.code
    history := p.loader.data.history
    temp := p.loader.data.temp
    execution := {s.execution with core := {s.execution.core with
      core := p.loader.data.core
      tape := p.loader.tape
      leftAddress := p.loader.address
      saved := p.loader.saved
      copyTemp := p.loader.copyTemp
      record := p.loader.record
      numWork := p.loader.numWork
      denWork := p.loader.denWork
      readPhase := p.loader.readPhase
      seekPhase := p.loader.seekPhase
      splitPhase := p.loader.splitPhase}}}

def dispatch (s : State W) : State W :=
  {s with loading := false, execution := {s.execution with core := {s.execution.core with
    readPhase := .halt, seekPhase := .halt, splitPhase := .halt}}}

def step (s : State W) : State W :=
  if s.loading then
    if s.pairPhase = .halt then dispatch W s
    else setPair W s (BinaryInterpreterOperandPair.step (pairView W s))
  else {s with execution := BinaryInterpreterArithmeticClean.step W s.execution}

def transitionTrace (s : State W) : List BinaryArithmetic.BitOp :=
  if s.loading then
    if s.pairPhase = .halt then [.branch]
    else .branch :: BinaryInterpreterOperandPair.transitionTrace (pairView W s)
  else BinaryInterpreterArithmeticClean.transitionTrace W s.execution

def advance : ℕ → State W → State W
  | 0, s => s
  | n+1, s => advance n (step W s)
def bitSteps : ℕ → State W → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace W s).length + bitSteps n (step W s)

def initial (tape : List Symbol) (destination : List Bool) (code history : List Symbol) : State W :=
  ⟨true, BinaryInterpreterArithmeticClean.runningState W
    {BinaryInterpreterArithmetic.operatingState L
      (L.initial BinaryInterpreterArithmetic.emptyWord BinaryInterpreterArithmetic.emptyWord) tape destination with
      readPhase := .reading, seekPhase := .seek, splitPhase := .sign},
    .left, .kind, .sign, .reading, code, history, []⟩

theorem view_set (s : State W) (p : BinaryInterpreterOperandPair.State L) :
    pairView W (setPair W s p) = p := by cases p; rfl
theorem set_set (s : State W) (p q : BinaryInterpreterOperandPair.State L) :
    setPair W (setPair W s p) q = setPair W s q := rfl
theorem set_view (s : State W) : setPair W s (pairView W s) = s := rfl

theorem advance_add (m n : ℕ) (s : State W) : advance W (m+n) s = advance W n (advance W m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step W s)
theorem bitSteps_add (m n : ℕ) (s : State W) :
    bitSteps W (m+n) s = bitSteps W m s + bitSteps W n (advance W m s) := by
  induction m generalizing s with
  | zero => simp [advance, bitSteps]
  | succ m ih => simp [Nat.succ_add, advance, bitSteps, ih, Nat.add_assoc]

def loadLift (frame : State W) (p : BinaryInterpreterOperandPair.State L) : State W :=
  {setPair W frame p with loading := true}

theorem load_step (frame : State W) (p : BinaryInterpreterOperandPair.State L) (h : p.phase ≠ .halt) :
    step W (loadLift W frame p) = loadLift W frame (BinaryInterpreterOperandPair.step p) := by
  simp only [step, loadLift, setPair, if_true, h, if_false]
  rfl

theorem pair_halt (n : ℕ) (p : BinaryInterpreterOperandPair.State L) (h : p.phase = .halt) :
    BinaryInterpreterOperandPair.advance n p = p := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterOperandPair.advance, BinaryInterpreterOperandPair.step, h] using ih

theorem forward_load (frame : State W) (p : BinaryInterpreterOperandPair.State L) (n : ℕ)
    (h : (BinaryInterpreterOperandPair.advance n p).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance W k (loadLift W frame p) =
      dispatch W (loadLift W frame (BinaryInterpreterOperandPair.advance n p)) ∧
      bitSteps W k (loadLift W frame p) ≤ 17*n+1 := by
  induction n generalizing p with
  | zero =>
    change p.phase = .halt at h
    refine ⟨1, by omega, ?_, ?_⟩
    · simp [advance, step, loadLift, setPair, h, BinaryInterpreterOperandPair.advance]
    · simp [bitSteps, transitionTrace, loadLift, setPair, h, BinaryInterpreterOperandPair.advance] at *
  | succ n ih =>
    by_cases hh : p.phase = .halt
    · rw [pair_halt (n+1) p hh]
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [advance, step, loadLift, setPair, hh]
      · simp [bitSteps, transitionTrace, loadLift, setPair, hh]
    · obtain ⟨k, hk, he, hc⟩ := ih (BinaryInterpreterOperandPair.step p) h
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [advance, load_step W frame p hh]
        exact he
      · have ht := BinaryInterpreterOperandPair.transition_length p
        rw [bitSteps, load_step W frame p hh]
        have hv : pairView W (loadLift W frame p) = p := view_set W frame p
        simp only [transitionTrace, loadLift, setPair, if_true, hh, if_false]
        change (BinaryInterpreterOperandPair.transitionTrace (pairView W (loadLift W frame p))).length + 1 +
          bitSteps W k (loadLift W frame (BinaryInterpreterOperandPair.step p)) ≤ _
        rw [hv]
        omega

theorem advance_execution (n : ℕ) (s : State W) (h : s.loading = false) :
    advance W n s = {s with execution := BinaryInterpreterArithmeticClean.advance W n s.execution} := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [advance, ih (step W s) (by simp [step, h])]
    simp [step, h, BinaryInterpreterArithmeticClean.advance]

theorem bitSteps_execution (n : ℕ) (s : State W) (h : s.loading = false) :
    bitSteps W n s = BinaryInterpreterArithmeticClean.bitSteps W n s.execution := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [bitSteps, transitionTrace, step, h, ih, BinaryInterpreterArithmeticClean.bitSteps]

end IdentityTesting.BinaryInterpreterOperandExecute
