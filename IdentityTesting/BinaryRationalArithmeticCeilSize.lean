import IdentityTesting.BinaryDivisionMachineBound
import IdentityTesting.BinaryRationalArithmeticBitLengthRuns
import IdentityTesting.BinaryRationalArithmeticCeilSemantics

/-! Ceiling precision is computed from the stored rational: long division,
remainder test, ripple-carry rounding, canonical normalization, and bit count.
Every movement between subroutines is an explicit per-cell loop. -/
namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic

inductive Phase where
  | test | dividing | quotientCollect | quotientEmit | round | incrementing
  | roundedCollect | roundedEmit | normalize | ceilingCollect | ceilingEmit
  | measuring | denominator | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  negative : Bool
  div : BinaryDivisionMachine.State
  counter : BinaryRationalArithmeticBitCounter.State
  norm : BinaryWordNormalization.State
  measure : BinaryRationalArithmeticBitLength.State
  temp : List Bool
  denominator : List Bool
  deriving DecidableEq, Repr

def initial (q : BinaryRationalArithmetic.Word) : State :=
  ⟨.test,q.numerator.negative,BinaryDivisionMachine.initial q.numerator.magnitude q.denominator,
    ⟨.increment,[],[],[]⟩,⟨.collect,[],[],[]⟩,BinaryRationalArithmeticBitLength.initial [],[],[]⟩

def step (s : State) : State :=
  match s.phase with
  | .test => if s.negative then {s with phase := .denominator} else {s with phase := .dividing}
  | .dividing => if s.div.phase = .halt then {s with phase := .quotientCollect}
      else {s with div := BinaryDivisionMachine.step s.div}
  | .quotientCollect => match s.div.quot.out with
      | [] => {s with phase := .quotientEmit}
      | b::bs => {s with div := {s.div with quot := {s.div.quot with out := bs}},temp := b::s.temp}
  | .quotientEmit => match s.temp with
      | [] => {s with phase := .round}
      | b::bs => {s with counter := {s.counter with counter := b::s.counter.counter},temp := bs}
  | .round => if s.div.rem.out = [] then {s with phase := .roundedCollect}
      else {s with phase := .incrementing}
  | .incrementing => if s.counter.phase = .halt then {s with phase := .roundedCollect}
      else {s with counter := BinaryRationalArithmeticBitCounter.step s.counter}
  | .roundedCollect => match s.counter.counter with
      | [] => {s with phase := .roundedEmit}
      | b::bs => {s with counter := {s.counter with counter := bs},temp := b::s.temp}
  | .roundedEmit => match s.temp with
      | [] => {s with phase := .normalize}
      | b::bs => {s with norm := {s.norm with source := b::s.norm.source},temp := bs}
  | .normalize => if s.norm.phase = .halt then {s with phase := .ceilingCollect}
      else {s with norm := BinaryWordNormalization.step s.norm}
  | .ceilingCollect => match s.norm.out with
      | [] => {s with phase := .ceilingEmit}
      | b::bs => {s with norm := {s.norm with out := bs},temp := b::s.temp}
  | .ceilingEmit => match s.temp with
      | [] => {s with phase := .measuring}
      | b::bs => {s with measure := {s.measure with core := {s.measure.core with source := b::s.measure.core.source}},temp := bs}
  | .measuring => if s.measure.phase = .halt then {s with phase := .denominator}
      else {s with measure := BinaryRationalArithmeticBitLength.step s.measure}
  | .denominator => {s with phase := .halt,denominator := true::s.denominator}
  | .halt => s

def output (s : State) : BinaryRationalArithmetic.Word :=
  ⟨⟨false,BinaryRationalArithmeticBitLength.output s.measure⟩,s.denominator⟩

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s=t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .test => [.readCell,.branch]
  | .dividing => if s.div.phase = .halt then [.branch] else .branch::BinaryDivisionMachine.transitionTrace s.div
  | .incrementing => if s.counter.phase = .halt then [.branch] else .branch::BinaryRationalArithmeticBitCounter.transitionTrace s.counter
  | .normalize => if s.norm.phase = .halt then [.branch] else .branch::BinaryWordNormalization.transitionTrace s.norm
  | .measuring => if s.measure.phase = .halt then [.branch] else .branch::BinaryRationalArithmeticBitLength.transitionTrace s.measure
  | .round => [.readCell,.branch]
  | .denominator => [.writeCell,.moveHead]
  | .halt => []
  | _ => [.readCell,.branch,.moveHead,.writeCell,.moveHead]

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 8 := by
  have hd := BinaryDivisionMachine.transition_length s.div
  have hc := BinaryRationalArithmeticBitCounter.transition_length s.counter
  have hn := BinaryWordNormalization.transition_length s.norm
  have hl := BinaryRationalArithmeticBitLength.transition_length s.measure
  cases hp:s.phase <;> simp only [transitionTrace,hp]
  all_goals first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 8*n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryRationalArithmeticCeilSize
