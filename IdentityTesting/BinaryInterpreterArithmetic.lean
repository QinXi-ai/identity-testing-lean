import IdentityTesting.BinaryInterpreterLayout

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryRegisterMachine (Cell Symbol)
open BinaryInterpreterLayout

inductive Phase where
  | left | right | operating | storing | halt
  deriving DecidableEq, Repr

structure State (L : Layout) where
  phase : Phase
  core : L.Core
  tape : List Symbol
  leftAddress : List Bool
  rightAddress : List Bool
  destination : List Bool
  saved : List Symbol
  copyTemp : List Cell
  record : List Cell
  numWork : List Bool
  denWork : List Bool
  negative : Bool
  readPhase : BinaryInterpreterRead.Phase
  seekPhase : BinaryRegisterMachine.Phase
  splitPhase : BinaryRationalRecordMachine.Phase
  storePhase : BinaryInterpreterWrite.Phase
  joinPhase : BinaryRationalRecordJoin.Phase
  writePhase : BinaryRegisterWriteMachine.Phase

variable {L : Layout}

def reader (s : State L) (right : Bool) : BinaryInterpreterRead.State :=
  ⟨s.readPhase, s.seekPhase, s.splitPhase, s.tape,
    if right then s.rightAddress else s.leftAddress,
    s.saved, s.copyTemp, s.record, (L.input right s.core).numerator.negative,
    s.numWork, s.denWork, (L.input right s.core).numerator.magnitude, (L.input right s.core).denominator⟩

def setReader (s : State L) (right : Bool) (r : BinaryInterpreterRead.State) : State L :=
  {s with
    core := L.setInput right s.core ⟨⟨r.negative,r.num⟩,r.den⟩
    tape := r.tape
    leftAddress := if right then s.leftAddress else r.address
    rightAddress := if right then r.address else s.rightAddress
    saved := r.saved
    copyTemp := r.copyTemp
    record := r.record
    numWork := r.numWork
    denWork := r.denWork
    readPhase := r.phase
    seekPhase := r.readPhase
    splitPhase := r.splitPhase}

def writer (s : State L) : BinaryInterpreterWrite.State :=
  ⟨s.storePhase, s.joinPhase, s.writePhase, s.tape, s.destination,
    s.saved, s.record, s.copyTemp, s.negative,
    (L.output s.core).numerator.magnitude, (L.output s.core).denominator, s.numWork⟩

def setWriter (s : State L) (w : BinaryInterpreterWrite.State) : State L :=
  {s with
    core := L.setOutput s.core w.num w.den
    tape := w.tape
    destination := w.address
    saved := w.saved
    record := w.record
    copyTemp := w.writeTemp
    numWork := w.joinTemp
    negative := w.negative
    storePhase := w.phase
    joinPhase := w.joinPhase
    writePhase := w.writePhase}

def step (s : State L) : State L :=
  match s.phase with
  | .left => if s.readPhase = .halt then
      {s with phase := .right, readPhase := .reading, seekPhase := .seek, splitPhase := .sign}
      else setReader s false (BinaryInterpreterRead.step (reader s false))
  | .right => if s.readPhase = .halt then {s with phase := .operating}
      else setReader s true (BinaryInterpreterRead.step (reader s true))
  | .operating => if L.halted s.core then
      {s with phase := .storing, negative := (L.output s.core).numerator.negative}
      else {s with core := L.step s.core}
  | .storing => if s.storePhase = .halt then {s with phase := .halt}
      else setWriter s (BinaryInterpreterWrite.step (writer s))
  | .halt => s

def transitionTrace (s : State L) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .left => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace (reader s false)
  | .right => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace (reader s true)
  | .operating => if L.halted s.core then [.branch,.readCell,.writeCell]
      else .branch :: L.trace s.core
  | .storing => if s.storePhase = .halt then [.branch]
      else .branch :: BinaryInterpreterWrite.transitionTrace (writer s)
  | .halt => []

def advance : ℕ → State L → State L
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State L → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

theorem advance_add (m n : ℕ) (s : State L) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem bitSteps_add (m n : ℕ) (s : State L) :
    bitSteps (m+n) s = bitSteps m s + bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance, bitSteps]
  | succ m ih => simp [Nat.succ_add, advance, bitSteps, ih, Nat.add_assoc]

def emptyWord : Word := ⟨⟨false,[]⟩,[]⟩
def initial (L : Layout) (tape : List Symbol) (a b dst : List Bool) : State L :=
  ⟨.left, L.initial emptyWord emptyWord, tape, a, b, dst, [], [], [], [], [], false,
    .reading, .seek, .sign, .joining, .denCollect, .seek⟩

theorem transitionTrace_length (s : State L) : (transitionTrace s).length ≤ 32 := by
  have hl := BinaryInterpreterRead.transitionTrace_length (reader s false)
  have hr := BinaryInterpreterRead.transitionTrace_length (reader s true)
  have hm := L.trace_bound s.core
  have hw := BinaryInterpreterWrite.transitionTrace_length (writer s)
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem bitSteps_le (n : ℕ) (s : State L) : bitSteps n s ≤ 32*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

end IdentityTesting.BinaryInterpreterArithmetic
