import IdentityTesting.BinaryRationalRecordJoin

/-! A shared record stack joins numerator/denominator output and then supplies
the replacement to register writeback. Switching phases changes control only. -/
namespace IdentityTesting.BinaryInterpreterWrite
open BinaryRegisterMachine (Cell Symbol)

inductive Phase where
  | joining | writing | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  joinPhase : BinaryRationalRecordJoin.Phase
  writePhase : BinaryRegisterWriteMachine.Phase
  tape : List Symbol
  address : List Bool
  saved : List Symbol
  record : List Cell
  writeTemp : List Cell
  negative : Bool
  num : List Bool
  den : List Bool
  joinTemp : List Bool
  deriving DecidableEq, Repr

def joiner (s : State) : BinaryRationalRecordJoin.State :=
  ⟨s.joinPhase, s.negative, s.num, s.den, s.joinTemp, s.record⟩
def writer (s : State) : BinaryRegisterWriteMachine.State :=
  ⟨s.writePhase, s.tape, s.address, s.saved, s.record, s.writeTemp⟩
def setJoiner (s : State) (r : BinaryRationalRecordJoin.State) : State :=
  {s with joinPhase := r.phase, negative := r.negative, num := r.num, den := r.den, joinTemp := r.temp, record := r.out}
def setWriter (s : State) (r : BinaryRegisterWriteMachine.State) : State :=
  {s with writePhase := r.phase, tape := r.tape, address := r.address, saved := r.saved, record := r.replacement, writeTemp := r.temp}

def step (s : State) : State :=
  match s.phase with
  | .joining => if s.joinPhase = .halt then {s with phase := .writing}
      else setJoiner s (BinaryRationalRecordJoin.step (joiner s))
  | .writing => if s.writePhase = .halt then {s with phase := .halt}
      else setWriter s (BinaryRegisterWriteMachine.step (writer s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .joining => if s.joinPhase = .halt then [.branch]
      else .branch :: BinaryRationalRecordJoin.transitionTrace (joiner s)
  | .writing => if s.writePhase = .halt then [.branch]
      else .branch :: BinaryRegisterWriteMachine.transitionTrace (writer s)
  | .halt => []

def advance : ℕ → State → State
  | 0, s => s
  | n+1, s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def joiningState (tape : List Symbol) (address : List Bool) (r : BinaryRationalRecordJoin.State) : State :=
  ⟨.joining, r.phase, .seek, tape, address, [], r.out, [], r.negative, r.num, r.den, r.temp⟩
def writingState (sign : Bool) (r : BinaryRegisterWriteMachine.State) : State :=
  ⟨.writing, .halt, r.phase, r.tape, r.address, r.saved, r.replacement, r.temp, sign, [], [], []⟩
def initial (tape : List Symbol) (address : List Bool) (word : BinaryRationalArithmetic.Word) : State :=
  joiningState tape address (BinaryRationalRecordJoin.initial word)
def haltState (sign : Bool) (tape : List Symbol) : State :=
  ⟨.halt, .halt, .halt, tape, [], [], [], [], sign, [], [], []⟩

theorem joiner_advance_halt (n : ℕ) (r : BinaryRationalRecordJoin.State) (h : r.phase = .halt) :
    BinaryRationalRecordJoin.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRationalRecordJoin.advance, BinaryRationalRecordJoin.step, h] using ih

theorem forward_join (r : BinaryRationalRecordJoin.State) (n : ℕ) (tape : List Symbol)
    (address : List Bool) (sign : Bool) (word : List Cell)
    (h : BinaryRationalRecordJoin.advance n r = BinaryRationalRecordJoin.haltState sign word) :
    ∃ k, k ≤ n+1 ∧ advance k (joiningState tape address r) =
      writingState sign (BinaryRegisterWriteMachine.seekState tape address [] word) := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryRationalRecordJoin.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [joiner_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryRationalRecordJoin.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, joiningState, joiner, setJoiner, hh] using he

theorem writer_advance_halt (n : ℕ) (r : BinaryRegisterWriteMachine.State) (h : r.phase = .halt) :
    BinaryRegisterWriteMachine.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRegisterWriteMachine.advance, BinaryRegisterWriteMachine.step, h] using ih

theorem forward_write (r : BinaryRegisterWriteMachine.State) (n : ℕ) (tape : List Symbol)
    (sign : Bool) (h : BinaryRegisterWriteMachine.advance n r = BinaryRegisterWriteMachine.haltState tape) :
    ∃ k, k ≤ n+1 ∧ advance k (writingState sign r) = haltState sign tape := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryRegisterWriteMachine.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [writer_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryRegisterWriteMachine.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, writingState, writer, setWriter, hh] using he

end IdentityTesting.BinaryInterpreterWrite
