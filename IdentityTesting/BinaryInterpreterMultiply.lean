import IdentityTesting.BinaryInterpreterCopyRuns
import IdentityTesting.BinaryRationalArithmeticMultiplierBound
import IdentityTesting.BinaryRationalArithmeticCanonical

/-! A register multiplication machine. Loader output stacks are the physical
input stacks of the multiplier; the writer reads its physical output stacks.
Switching phases changes finite control only. Addresses are explicit unary tapes.
Arithmetic scratch remains present after writeback, for subsequent cleanup. -/
namespace IdentityTesting.BinaryInterpreterMultiply
open BinaryRegisterMachine (Cell Symbol)

inductive Phase where
  | left | right | multiplying | storing | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryRationalArithmeticMultiplier.State
  tape : List Symbol
  leftAddress : List Bool
  rightAddress : List Bool
  destination : List Bool
  saved : List Symbol
  copyTemp : List Cell
  record : List Cell
  numWork : List Bool
  denWork : List Bool
  readPhase : BinaryInterpreterRead.Phase
  seekPhase : BinaryRegisterMachine.Phase
  splitPhase : BinaryRationalRecordMachine.Phase
  storePhase : BinaryInterpreterWrite.Phase
  joinPhase : BinaryRationalRecordJoin.Phase
  writePhase : BinaryRegisterWriteMachine.Phase
  deriving DecidableEq, Repr

def reader (s : State) (right : Bool) : BinaryInterpreterRead.State :=
  ⟨s.readPhase, s.seekPhase, s.splitPhase, s.tape,
    if right then s.rightAddress else s.leftAddress,
    s.saved, s.copyTemp, s.record,
    if right then s.core.num.signRight else s.core.num.signLeft,
    s.numWork, s.denWork,
    if right then s.core.num.mul.shifted else s.core.num.mul.factor,
    if right then s.core.den.mul.shifted else s.core.den.mul.factor⟩

def setReader (s : State) (right : Bool) (r : BinaryInterpreterRead.State) : State :=
  {s with
    core := if right then
      {s.core with num := {s.core.num with signRight := r.negative, mul := {s.core.num.mul with shifted := r.num}}, den := {s.core.den with mul := {s.core.den.mul with shifted := r.den}}}
      else {s.core with num := {s.core.num with signLeft := r.negative, mul := {s.core.num.mul with factor := r.num}}, den := {s.core.den with mul := {s.core.den.mul with factor := r.den}}}
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

def writer (s : State) : BinaryInterpreterWrite.State :=
  ⟨s.storePhase, s.joinPhase, s.writePhase, s.tape, s.destination,
    s.saved, s.record, s.copyTemp, s.core.norm.negative,
    s.core.norm.num.quot.out, s.core.norm.den.quot.out, s.numWork⟩

def setWriter (s : State) (w : BinaryInterpreterWrite.State) : State :=
  {s with
    core := {s.core with norm := {s.core.norm with negative := w.negative, num := {s.core.norm.num with quot := {s.core.norm.num.quot with out := w.num}}, den := {s.core.norm.den with quot := {s.core.norm.den.quot with out := w.den}}}}
    tape := w.tape
    destination := w.address
    saved := w.saved
    record := w.record
    copyTemp := w.writeTemp
    numWork := w.joinTemp
    storePhase := w.phase
    joinPhase := w.joinPhase
    writePhase := w.writePhase}

def step (s : State) : State :=
  match s.phase with
  | .left => if s.readPhase = .halt then
      {s with phase := .right, readPhase := .reading, seekPhase := .seek, splitPhase := .sign}
      else setReader s false (BinaryInterpreterRead.step (reader s false))
  | .right => if s.readPhase = .halt then {s with phase := .multiplying}
      else setReader s true (BinaryInterpreterRead.step (reader s true))
  | .multiplying => if s.core.phase = .halt then {s with phase := .storing}
      else {s with core := BinaryRationalArithmeticMultiplier.step s.core}
  | .storing => if s.storePhase = .halt then {s with phase := .halt}
      else setWriter s (BinaryInterpreterWrite.step (writer s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .left => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace (reader s false)
  | .right => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace (reader s true)
  | .multiplying => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticMultiplier.transitionTrace s.core
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

theorem bitSteps_add (m n : ℕ) (s : State) :
    bitSteps (m+n) s = bitSteps m s + bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance, bitSteps]
  | succ m ih => simp [Nat.succ_add, advance, bitSteps, ih, Nat.add_assoc]

def emptyWord : BinaryRationalArithmetic.Word := ⟨⟨false, []⟩, []⟩

def initial (tape : List Symbol) (left right destination : List Bool) : State :=
  ⟨.left, BinaryRationalArithmeticMultiplier.initial emptyWord emptyWord,
    tape, left, right, destination, [], [], [], [], [], .reading, .seek, .sign,
    .joining, .denCollect, .seek⟩

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 15 := by
  have hl := BinaryInterpreterRead.transitionTrace_length (reader s false)
  have hr := BinaryInterpreterRead.transitionTrace_length (reader s true)
  have hm := BinaryRationalArithmeticMultiplier.transition_length s.core
  have hw := BinaryInterpreterWrite.transitionTrace_length (writer s)
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

end IdentityTesting.BinaryInterpreterMultiply
