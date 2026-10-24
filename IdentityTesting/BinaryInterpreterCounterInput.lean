import IdentityTesting.BinaryInterpreterCopyRuns
import IdentityTesting.BinaryRationalArithmeticNatCounter

/-! A natural-valued rational register is read into a shared binary counter.
The reader's numerator output is the physical countdown stack; its denominator
is cleared one cell at a time. This component does not claim arbitrary rational
floor conversion. The actual allocation counters satisfy its naturalness premise. -/
namespace IdentityTesting.BinaryInterpreterCounterInput
open BinaryRegisterMachine BinaryRationalRegisters RationalComputation

inductive Phase where
  | reading | clearing | counting | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  reader : BinaryInterpreterRead.State
  counterPhase : BinaryRationalArithmeticNatCounter.Phase
  temp : List Bool
  zero : Bool
  deriving DecidableEq, Repr

def counter (s : State) : BinaryRationalArithmeticNatCounter.State :=
  ⟨s.counterPhase,s.reader.num,s.temp,s.zero⟩
def setCounter (s : State) (c : BinaryRationalArithmeticNatCounter.State) : State :=
  {s with reader := {s.reader with num := c.counter},counterPhase := c.phase,temp := c.temp,zero := c.zero}

def step (s : State) : State :=
  match s.phase with
  | .reading => if s.reader.phase = .halt then {s with phase := .clearing}
      else {s with reader := BinaryInterpreterRead.step s.reader}
  | .clearing => match s.reader.den with
      | [] => {s with phase := .halt}
      | _::ds => {s with reader := {s.reader with den := ds}}
  | .counting => if s.counterPhase = .halt then {s with phase := .halt}
      else setCounter s (BinaryRationalArithmeticNatCounter.step (counter s))
  | .halt => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .reading => if s.reader.phase = .halt then [.branch]
      else .branch :: BinaryInterpreterRead.transitionTrace s.reader
  | .clearing => if s.reader.den = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead]
  | .counting => if s.counterPhase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticNatCounter.transitionTrace (counter s)
  | .halt => []
def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

def readingState (r : BinaryInterpreterRead.State) : State := ⟨.reading,r,.check,[],false⟩
def clearingState (r : BinaryInterpreterRead.State) : State := ⟨.clearing,r,.check,[],false⟩
def initial (tape : List Symbol) (address : List Bool) : State :=
  readingState (BinaryInterpreterRead.initial tape address)
def haltState (tape : List Symbol) (bits : List Bool) : State :=
  ⟨.halt,BinaryInterpreterRead.haltState tape ⟨⟨false,bits⟩,[]⟩,.check,[],false⟩

def Clean (s : State) : Prop :=
  s.reader.address = [] ∧ s.reader.saved = [] ∧ s.reader.copyTemp = [] ∧
  s.reader.record = [] ∧ s.reader.numWork = [] ∧ s.reader.denWork = [] ∧
  s.reader.den = [] ∧ s.temp = []

def rearmTest (s : State) : State := {s with phase := .counting,counterPhase := .check,zero := false}
def rearmPred (s : State) : State := {s with phase := .counting,counterPhase := .pred,zero := false}

theorem rearm_stacks (s : State) :
    (rearmTest s).reader = s.reader ∧ (rearmTest s).temp = s.temp ∧
    (rearmPred s).reader = s.reader ∧ (rearmPred s).temp = s.temp := ⟨rfl,rfl,rfl,rfl⟩

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)
theorem bitSteps_add (m n : ℕ) (s : State) : bitSteps (m+n) s=bitSteps m s+bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance,bitSteps]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

theorem transition_length (s : State) : (transitionTrace s).length ≤ 15 := by
  have hr := BinaryInterpreterRead.transitionTrace_length s.reader
  have hc := BinaryRationalArithmeticNatCounter.transition_length (counter s)
  cases hp:s.phase <;> simp only [transitionTrace,hp]
  all_goals (repeat' first | split | simp_all | omega)
theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 15*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transition_length s
    have hi := ih (step s)
    simp only [bitSteps]
    omega

theorem read_halt (n : ℕ) (r : BinaryInterpreterRead.State) (h : r.phase = .halt) :
    BinaryInterpreterRead.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterRead.advance,BinaryInterpreterRead.step,h] using ih

theorem forward_read (r : BinaryInterpreterRead.State) (n : ℕ)
    (h : (BinaryInterpreterRead.advance n r).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (readingState r) = clearingState (BinaryInterpreterRead.advance n r) := by
  induction n generalizing r with
  | zero =>
    change r.phase = .halt at h
    exact ⟨1,by omega,by simp [advance,step,readingState,clearingState,h,BinaryInterpreterRead.advance]⟩
  | succ n ih =>
    by_cases hh : r.phase = .halt
    · rw [read_halt (n+1) r hh]
      exact ⟨1,by omega,by simp [advance,step,readingState,clearingState,hh]⟩
    · obtain ⟨k,hk,he⟩ := ih (BinaryInterpreterRead.step r) h
      refine ⟨k+1,by omega,?_⟩
      simpa [advance,step,readingState,hh] using he

end IdentityTesting.BinaryInterpreterCounterInput
