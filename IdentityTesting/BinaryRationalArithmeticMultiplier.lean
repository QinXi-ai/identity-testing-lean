import IdentityTesting.BinaryRationalArithmeticWords
import IdentityTesting.BinarySignedMultiplierRuns

/-! Rational multiplication from two signed binary multipliers followed by the
proved gcd/exact-division normalization machine. The four output-to-input
transfers below each move one bit per transition. -/
namespace IdentityTesting.BinaryRationalArithmeticMultiplier
open BinaryArithmetic

inductive Phase where
  | numerator | denominator | numCollect | numEmit | denCollect | denEmit | normalize | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  num : BinarySignedMultiplier.State
  den : BinarySignedMultiplier.State
  norm : BinaryRationalNormalizationMachine.State
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .numerator => if s.num.phase = .halt then { s with phase := .denominator }
      else { s with num := BinarySignedMultiplier.step s.num }
  | .denominator => if s.den.phase = .halt then
      { s with phase := .numCollect, norm := { s.norm with negative := s.num.negative } }
      else { s with den := BinarySignedMultiplier.step s.den }
  | .numCollect => match s.num.norm.out with
      | [] => { s with phase := .numEmit }
      | b :: bs => { s with temp := b :: s.temp, num := { s.num with norm := { s.num.norm with out := bs } } }
  | .numEmit => match s.temp with
      | [] => { s with phase := .denCollect }
      | b :: bs => { s with temp := bs, norm := { s.norm with num := { s.norm.num with source := b :: s.norm.num.source } } }
  | .denCollect => match s.den.norm.out with
      | [] => { s with phase := .denEmit }
      | b :: bs => { s with temp := b :: s.temp, den := { s.den with norm := { s.den.norm with out := bs } } }
  | .denEmit => match s.temp with
      | [] => { s with phase := .normalize }
      | b :: bs => { s with temp := bs, norm := { s.norm with den := { s.norm.den with source := b :: s.norm.den.source } } }
  | .normalize => if s.norm.phase = .halt then { s with phase := .halt }
      else { s with norm := BinaryRationalNormalizationMachine.step s.norm }
  | .halt => s

def initial (x y : BinaryRationalArithmetic.Word) : State :=
  ⟨.numerator,
    BinarySignedMultiplier.initial x.numerator.negative y.numerator.negative x.numerator.magnitude y.numerator.magnitude,
    BinarySignedMultiplier.initial false false x.denominator y.denominator,
    BinaryRationalNormalizationMachine.initial false [] [], []⟩

def output (s : State) : BinaryRationalArithmetic.Word :=
  ⟨⟨s.norm.negative,s.norm.num.quot.out⟩,s.norm.den.quot.out⟩

def advance : ℕ → State → State
  | 0, s => s
  | n+1, s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s = t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .numerator => if s.num.phase = .halt then [.branch] else .branch :: BinarySignedMultiplier.transitionTrace s.num
  | .denominator => if s.den.phase = .halt then [.branch,.readCell,.writeCell] else .branch :: BinarySignedMultiplier.transitionTrace s.den
  | .numCollect => match s.num.norm.out with
      | [] => [.readCell,.branch]
      | _::_ => [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .denCollect => match s.den.norm.out with
      | [] => [.readCell,.branch]
      | _::_ => [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .numEmit | .denEmit => match s.temp with
      | [] => [.readCell,.branch]
      | _::_ => [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .normalize => if s.norm.phase = .halt then [.branch] else .branch :: BinaryRationalNormalizationMachine.transitionTrace s.norm
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 10 := by
  have hn := BinarySignedMultiplier.transition_length s.num
  have hd := BinarySignedMultiplier.transition_length s.den
  have hr := BinaryRationalNormalizationMachine.transition_length s.norm
  cases hp : s.phase <;> simp only [transitionTrace,hp] <;>
    first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 10*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryRationalArithmeticMultiplier
