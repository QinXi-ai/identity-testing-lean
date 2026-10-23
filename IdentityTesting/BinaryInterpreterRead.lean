import IdentityTesting.BinaryRationalRecordJoin

/-! Combined register read and rational-record parsing. The record stack is
shared between the two phases: switching control does not move or reset it.
The remaining stacks stay present in both phases, including scratch tapes. -/
namespace IdentityTesting.BinaryInterpreterRead
open BinaryRegisterMachine (Cell Symbol)

inductive Phase where
  | reading | splitting | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  readPhase : BinaryRegisterMachine.Phase
  splitPhase : BinaryRationalRecordMachine.Phase
  tape : List Symbol
  address : List Bool
  saved : List Symbol
  copyTemp : List Cell
  record : List Cell
  negative : Bool
  numWork : List Bool
  denWork : List Bool
  num : List Bool
  den : List Bool
  deriving DecidableEq, Repr

def reader (s : State) : BinaryRegisterMachine.State :=
  ⟨s.readPhase, s.tape, s.address, s.saved, s.copyTemp, s.record⟩
def splitter (s : State) : BinaryRationalRecordMachine.State :=
  ⟨s.splitPhase, s.record, s.negative, s.numWork, s.denWork, s.num, s.den⟩

def setReader (s : State) (r : BinaryRegisterMachine.State) : State :=
  {s with readPhase := r.phase, tape := r.tape, address := r.address, saved := r.saved, copyTemp := r.temp, record := r.out}
def setSplitter (s : State) (r : BinaryRationalRecordMachine.State) : State :=
  {s with splitPhase := r.phase, record := r.input, negative := r.negative, numWork := r.numWork, denWork := r.denWork, num := r.num, den := r.den}

def step (s : State) : State :=
  match s.phase with
  | .reading => if s.readPhase = .halt then {s with phase := .splitting}
      else setReader s (BinaryRegisterMachine.step (reader s))
  | .splitting => if s.splitPhase = .halt then {s with phase := .halt}
      else setSplitter s (BinaryRationalRecordMachine.step (splitter s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .reading => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryRegisterMachine.transitionTrace (reader s)
  | .splitting => if s.splitPhase = .halt then [.branch]
      else .branch :: BinaryRationalRecordMachine.transitionTrace (splitter s)
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

def initial (tape : List Symbol) (address : List Bool) : State :=
  ⟨.reading, .seek, .sign, tape, address, [], [], [], false, [], [], [], []⟩

def readingState (r : BinaryRegisterMachine.State) : State :=
  ⟨.reading, r.phase, .sign, r.tape, r.address, r.saved, r.temp, r.out, false, [], [], [], []⟩

def splittingState (tape : List Symbol) (r : BinaryRationalRecordMachine.State) : State :=
  ⟨.splitting, .halt, r.phase, tape, [], [], [], r.input, r.negative,
    r.numWork, r.denWork, r.num, r.den⟩

def haltState (tape : List Symbol) (word : BinaryRationalArithmetic.Word) : State :=
  ⟨.halt, .halt, .halt, tape, [], [], [], [], word.numerator.negative, [], [],
    word.numerator.magnitude, word.denominator⟩

theorem reader_advance_halt (n : ℕ) (r : BinaryRegisterMachine.State) (h : r.phase = .halt) :
    BinaryRegisterMachine.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRegisterMachine.advance, BinaryRegisterMachine.step, h] using ih

theorem forward_read (r : BinaryRegisterMachine.State) (n : ℕ) (tape : List Symbol) (word : List Cell)
    (h : BinaryRegisterMachine.advance n r = BinaryRegisterMachine.haltState tape word) :
    ∃ k, k ≤ n+1 ∧ advance k (readingState r) =
      splittingState tape (BinaryRationalRecordMachine.initial word) := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryRegisterMachine.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [reader_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryRegisterMachine.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, readingState, reader, setReader, hh] using he

theorem splitter_advance_halt (n : ℕ) (r : BinaryRationalRecordMachine.State) (h : r.phase = .halt) :
    BinaryRationalRecordMachine.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryRationalRecordMachine.advance, BinaryRationalRecordMachine.step, h] using ih

theorem forward_split (r : BinaryRationalRecordMachine.State) (n : ℕ) (tape : List Symbol)
    (word : BinaryRationalArithmetic.Word)
    (h : BinaryRationalRecordMachine.advance n r =
      BinaryRationalRecordMachine.haltState word.numerator.negative word.numerator.magnitude word.denominator) :
    ∃ k, k ≤ n+1 ∧ advance k (splittingState tape r) = haltState tape word := by
  induction n generalizing r with
  | zero =>
    simp only [BinaryRationalRecordMachine.advance] at h
    subst r
    exact ⟨1, by omega, rfl⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [splitter_advance_halt _ r hh] at h
      subst r
      exact ⟨1, by omega, rfl⟩
    · obtain ⟨k, hk, he⟩ := ih (BinaryRationalRecordMachine.step r) h
      refine ⟨k+1, by omega, ?_⟩
      rw [advance]
      simpa [step, splittingState, splitter, setSplitter, hh] using he

end IdentityTesting.BinaryInterpreterRead
