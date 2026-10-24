import IdentityTesting.BinaryInterpreterLiteralInput
import IdentityTesting.BinaryCodeMaterialization

/-! A single operand loader consumes its discriminator from the program tape.
The address loader, register reader and literal loader share their actual
stacks. The selected arithmetic input is the output of either branch. -/
namespace IdentityTesting.BinaryInterpreterOperand
open BinaryInterpreterLayout BinaryRegisterMachine

inductive Phase where
  | kind | delimiter (literal : Bool) | address | reading | literal | halt | invalid
  deriving DecidableEq, Repr

structure State (L : Layout) where
  phase : Phase
  data : BinaryInterpreterLiteralInput.State L
  tape : List Symbol
  address : List Bool
  saved : List Symbol
  copyTemp : List Cell
  record : List Cell
  numWork : List Bool
  denWork : List Bool
  readPhase : BinaryInterpreterRead.Phase
  seekPhase : BinaryRegisterMachine.Phase
  splitPhase : BinaryRationalRecordMachine.Phase

variable {L : Layout}

def wordView (s : State L) : BinaryCodeWordLoader.State :=
  ⟨s.data.fieldPhase, s.data.code, s.data.history, s.data.temp, s.address⟩
def setWord (s : State L) (w : BinaryCodeWordLoader.State) : State L :=
  { s with
    data := {s.data with fieldPhase := w.phase, code := w.code, history := w.history, temp := w.temp}
    address := w.out }

def readView (right : Bool) (s : State L) : BinaryInterpreterRead.State :=
  ⟨s.readPhase, s.seekPhase, s.splitPhase, s.tape, s.address, s.saved, s.copyTemp,
    s.record, (L.input right s.data.core).numerator.negative, s.numWork, s.denWork,
    (L.input right s.data.core).numerator.magnitude, (L.input right s.data.core).denominator⟩
def setRead (right : Bool) (s : State L) (r : BinaryInterpreterRead.State) : State L :=
  { s with
    data := {s.data with core := L.setInput right s.data.core ⟨⟨r.negative, r.num⟩, r.den⟩}
    tape := r.tape
    address := r.address
    saved := r.saved
    copyTemp := r.copyTemp
    record := r.record
    numWork := r.numWork
    denWork := r.denWork
    readPhase := r.phase
    seekPhase := r.readPhase
    splitPhase := r.splitPhase }

def step (right : Bool) (s : State L) : State L :=
  match s.phase with
  | .kind => match s.data.code with
      | .cell (.bit b) :: cs => { s with
          phase := .delimiter b
          data := {s.data with code := cs, history := .cell (.bit b) :: s.data.history} }
      | _ => {s with phase := .invalid}
  | .delimiter literal => match s.data.code with
      | .boundary :: cs => { s with
          phase := if literal then .literal else .address
          data := {s.data with code := cs, history := .boundary :: s.data.history} }
      | _ => {s with phase := .invalid}
  | .address => if s.data.fieldPhase = .halt then {s with phase := .reading}
      else setWord s (BinaryCodeWordLoader.step (wordView s))
  | .reading => if s.readPhase = .halt then {s with phase := .halt}
      else setRead right s (BinaryInterpreterRead.step (readView right s))
  | .literal => if s.data.phase = .halt then {s with phase := .halt}
      else {s with data := BinaryInterpreterLiteralInput.step right s.data}
  | .halt | .invalid => s

def transitionTrace (right : Bool) (s : State L) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .kind | .delimiter _ => [.readCell, .readCell, .branch, .moveHead, .writeCell, .writeCell, .moveHead]
  | .address => if s.data.fieldPhase = .halt then [.branch]
      else .branch :: BinaryCodeWordLoader.transitionTrace (wordView s)
  | .reading => if s.readPhase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace (readView right s)
  | .literal => if s.data.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterLiteralInput.transitionTrace right s.data
  | .halt | .invalid => []

def advance (right : Bool) : ℕ → State L → State L
  | 0, s => s
  | n+1, s => advance right n (step right s)
def bitSteps (right : Bool) : ℕ → State L → ℕ
  | 0, _ => 0
  | n+1, s => (transitionTrace right s).length + bitSteps right n (step right s)

def initial (c : L.Core) (tape code history : List Symbol) : State L :=
  ⟨.kind, BinaryInterpreterLiteralInput.initial c code history, tape, [], [], [], [], [], [],
    .reading, .seek, .sign⟩

def Clean (s : State L) : Prop :=
  s.data.temp = [] ∧ s.address = [] ∧ s.saved = [] ∧ s.copyTemp = [] ∧
    s.record = [] ∧ s.numWork = [] ∧ s.denWork = []

theorem advance_add (right : Bool) (m n : ℕ) (s : State L) :
    advance right (m+n) s = advance right n (advance right m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step right s)

theorem transition_length (right : Bool) (s : State L) : (transitionTrace right s).length ≤ 15 := by
  have hw := BinaryCodeWordLoader.transition_length (wordView s)
  have hr := BinaryInterpreterRead.transitionTrace_length (readView right s)
  have hl := BinaryCodeLiteralLoader.transition_length (BinaryInterpreterLiteralInput.view right s.data)
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinaryInterpreterLiteralInput.transitionTrace] | omega)

theorem bitSteps_le (right : Bool) (n : ℕ) (s : State L) : bitSteps right n s ≤ 15*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length right s
      have hi := ih (step right s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryInterpreterOperand
