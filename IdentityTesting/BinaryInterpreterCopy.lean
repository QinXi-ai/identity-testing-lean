import IdentityTesting.BinaryInterpreterIOFuel

/-! A real register-to-register copy instruction. Source load and destination
store share the tape and numerator/denominator stacks. The phase switch updates
finite control only. Both addresses are explicit input tapes. -/
namespace IdentityTesting.BinaryInterpreterCopy
open BinaryRegisterMachine (Symbol)

inductive Phase where
  | loading | storing | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryInterpreterRead.State
  destination : List Bool
  storePhase : BinaryInterpreterWrite.Phase
  joinPhase : BinaryRationalRecordJoin.Phase
  writePhase : BinaryRegisterWriteMachine.Phase
  deriving DecidableEq, Repr

def writer (s : State) : BinaryInterpreterWrite.State :=
  ⟨s.storePhase, s.joinPhase, s.writePhase, s.core.tape, s.destination, s.core.saved,
    s.core.record, s.core.copyTemp, s.core.negative, s.core.num, s.core.den, s.core.numWork⟩

def setWriter (s : State) (w : BinaryInterpreterWrite.State) : State :=
  {s with
    core := {s.core with tape := w.tape, saved := w.saved, copyTemp := w.writeTemp, record := w.record, negative := w.negative, numWork := w.joinTemp, num := w.num, den := w.den}
    destination := w.address
    storePhase := w.phase
    joinPhase := w.joinPhase
    writePhase := w.writePhase}

def step (s : State) : State :=
  match s.phase with
  | .loading => if s.core.phase = .halt then {s with phase := .storing}
      else {s with core := BinaryInterpreterRead.step s.core}
  | .storing => if s.storePhase = .halt then {s with phase := .halt}
      else setWriter s (BinaryInterpreterWrite.step (writer s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .loading => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace s.core
  | .storing => if s.storePhase = .halt then [.branch]
      else .branch :: BinaryInterpreterWrite.transitionTrace (writer s)
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

def loadingState (r : BinaryInterpreterRead.State) (dest : List Bool) : State :=
  ⟨.loading, r, dest, .joining, .denCollect, .seek⟩
def initial (tape : List Symbol) (source destination : List Bool) : State :=
  loadingState (BinaryInterpreterRead.initial tape source) destination
def storingState (w : BinaryInterpreterWrite.State) : State :=
  ⟨.storing, ⟨.halt, .halt, .halt, w.tape, [], w.saved, w.writeTemp, w.record,
    w.negative, w.joinTemp, [], w.num, w.den⟩, w.address, w.phase, w.joinPhase, w.writePhase⟩
def haltState (sign : Bool) (tape : List Symbol) : State :=
  ⟨.halt, BinaryInterpreterRead.haltState tape ⟨⟨sign, []⟩, []⟩, [], .halt, .halt, .halt⟩

theorem load_advance_halt (n : ℕ) (r : BinaryInterpreterRead.State) (h : r.phase = .halt) :
    BinaryInterpreterRead.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterRead.advance, BinaryInterpreterRead.step, h] using ih

theorem forward_load (r : BinaryInterpreterRead.State) (n : ℕ) (tape : List Symbol)
    (word : BinaryRationalArithmetic.Word) (dest : List Bool)
    (h : BinaryInterpreterRead.advance n r = BinaryInterpreterRead.haltState tape word) :
    ∃ k, k ≤ n+1 ∧ advance k (loadingState r dest) =
      storingState (BinaryInterpreterWrite.initial tape dest word) := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterRead.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [load_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, loadingState, hh] using he

theorem store_advance_halt (n : ℕ) (r : BinaryInterpreterWrite.State) (h : r.phase = .halt) :
    BinaryInterpreterWrite.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterWrite.advance, BinaryInterpreterWrite.step, h] using ih

theorem forward_store (r : BinaryInterpreterWrite.State) (n : ℕ) (tape : List Symbol)
    (sign : Bool) (h : BinaryInterpreterWrite.advance n r = BinaryInterpreterWrite.haltState sign tape) :
    ∃ k, k ≤ n+1 ∧ advance k (storingState r) = haltState sign tape := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryInterpreterWrite.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [store_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterWrite.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, storingState, writer, setWriter, hh] using he

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 15 := by
  have hl := BinaryInterpreterRead.transitionTrace_length s.core
  have hs := BinaryInterpreterWrite.transitionTrace_length (writer s)
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 15*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

end IdentityTesting.BinaryInterpreterCopy
