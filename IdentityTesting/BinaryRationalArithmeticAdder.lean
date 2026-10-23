import IdentityTesting.BinaryRationalArithmeticMultiplierBound
import IdentityTesting.BinarySignedAdderBound

/-! Rational addition with explicit denominator duplication, three product
runs, a signed sum, and normalization. All word transfers use single-bit loops. -/
namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic

inductive Phase where
  | pdenCollect | pdenCopy | qdenCollect | qdenCopy | leftProduct | rightProduct | denominator
  | leftCollect | leftEmit | rightCollect | rightEmit | add | sumCollect | sumEmit | normalize | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  base : BinaryRationalArithmeticMultiplier.State
  right : BinarySignedMultiplier.State
  adder : BinarySignedAdder.State
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .pdenCollect => match s.base.den.mul.factor with
      | [] => { s with phase := .pdenCopy }
      | b::bs => { s with temp := b::s.temp, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := bs } } } }
  | .pdenCopy => match s.temp with
      | [] => { s with phase := .qdenCollect }
      | b::bs => { s with temp := bs, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with factor := b::s.base.den.mul.factor } } }, right := { s.right with mul := { s.right.mul with shifted := b::s.right.mul.shifted } } }
  | .qdenCollect => match s.base.den.mul.shifted with
      | [] => { s with phase := .qdenCopy }
      | b::bs => { s with temp := b::s.temp, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := bs } } } }
  | .qdenCopy => match s.temp with
      | [] => { s with phase := .leftProduct }
      | b::bs => { s with temp := bs, base := { s.base with den := { s.base.den with mul := { s.base.den.mul with shifted := b::s.base.den.mul.shifted } }, num := { s.base.num with mul := { s.base.num.mul with shifted := b::s.base.num.mul.shifted } } } }
  | .leftProduct => if s.base.num.phase = .halt then { s with phase := .rightProduct }
      else { s with base := { s.base with num := BinarySignedMultiplier.step s.base.num } }
  | .rightProduct => if s.right.phase = .halt then { s with phase := .denominator }
      else { s with right := BinarySignedMultiplier.step s.right }
  | .denominator => if s.base.den.phase = .halt then
      { s with phase := .leftCollect, adder := { s.adder with negativeLeft := s.base.num.negative, negativeRight := s.right.negative } }
      else { s with base := { s.base with den := BinarySignedMultiplier.step s.base.den } }
  | .leftCollect => match s.base.num.norm.out with
      | [] => { s with phase := .leftEmit }
      | b::bs => { s with temp := b::s.temp, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := bs } } } }
  | .leftEmit => match s.temp with
      | [] => { s with phase := .rightCollect }
      | b::bs => { s with temp := bs, adder := { s.adder with left := b::s.adder.left } }
  | .rightCollect => match s.right.norm.out with
      | [] => { s with phase := .rightEmit }
      | b::bs => { s with temp := b::s.temp, right := { s.right with norm := { s.right.norm with out := bs } } }
  | .rightEmit => match s.temp with
      | [] => { s with phase := .add }
      | b::bs => { s with temp := bs, adder := { s.adder with right := b::s.adder.right } }
  | .add => if s.adder.phase = .halt then { s with phase := .sumCollect }
      else { s with adder := BinarySignedAdder.step s.adder }
  | .sumCollect => match s.adder.norm.out with
      | [] => { s with phase := .sumEmit }
      | b::bs => { s with temp := b::s.temp, adder := { s.adder with norm := { s.adder.norm with out := bs } } }
  | .sumEmit => match s.temp with
      | [] => { s with phase := .normalize, base := { s.base with num := { s.base.num with negative := s.adder.negative }, norm := { s.base.norm with negative := s.adder.negative } } }
      | b::bs => { s with temp := bs, base := { s.base with num := { s.base.num with norm := { s.base.num.norm with out := b::s.base.num.norm.out } } } }
  | .normalize => if s.base.phase = .halt then { s with phase := .halt }
      else { s with base := BinaryRationalArithmeticMultiplier.step s.base }
  | .halt => s

def initial (p q : BinaryRationalArithmetic.Word) : State :=
  ⟨.pdenCollect,
    ⟨.numCollect,
      BinarySignedMultiplier.initial p.numerator.negative false p.numerator.magnitude [],
      BinarySignedMultiplier.initial false false p.denominator q.denominator,
      BinaryRationalNormalizationMachine.initial false [] [],[]⟩,
    BinarySignedMultiplier.initial q.numerator.negative false q.numerator.magnitude [],
    BinarySignedAdder.initial ⟨false,[]⟩ ⟨false,[]⟩,[]⟩

def output (s : State) : BinaryRationalArithmetic.Word := BinaryRationalArithmeticMultiplier.output s.base

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s = t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .pdenCollect => if s.base.den.mul.factor = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .qdenCollect => if s.base.den.mul.shifted = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .pdenCopy | .qdenCopy => if s.temp = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead,.writeCell,.moveHead]
  | .leftProduct => if s.base.num.phase = .halt then [.branch] else .branch :: BinarySignedMultiplier.transitionTrace s.base.num
  | .rightProduct => if s.right.phase = .halt then [.branch] else .branch :: BinarySignedMultiplier.transitionTrace s.right
  | .denominator => if s.base.den.phase = .halt then [.branch,.readCell,.writeCell,.readCell,.writeCell]
      else .branch :: BinarySignedMultiplier.transitionTrace s.base.den
  | .leftCollect => if s.base.num.norm.out = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .rightCollect => if s.right.norm.out = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .sumCollect => if s.adder.norm.out = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .leftEmit | .rightEmit => if s.temp = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .sumEmit => if s.temp = [] then [.readCell,.branch,.readCell,.writeCell,.writeCell]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .add => if s.adder.phase = .halt then [.branch] else .branch :: BinarySignedAdder.transitionTrace s.adder
  | .normalize => if s.base.phase = .halt then [.branch] else .branch :: BinaryRationalArithmeticMultiplier.transitionTrace s.base
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 13 := by
  have hl := BinarySignedMultiplier.transition_length s.base.num
  have hr := BinarySignedMultiplier.transition_length s.right
  have hd := BinarySignedMultiplier.transition_length s.base.den
  have ha := BinarySignedAdder.transition_length s.adder
  have hb := BinaryRationalArithmeticMultiplier.transition_length s.base
  cases hp : s.phase <;> simp only [transitionTrace,hp] <;>
    first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 13*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryRationalArithmeticAdder
