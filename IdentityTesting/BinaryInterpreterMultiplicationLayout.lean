import IdentityTesting.BinaryInterpreterLayout
import IdentityTesting.BinaryRationalArithmeticMultiplierBound

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

def mulInput (right : Bool) (c : BinaryRationalArithmeticMultiplier.State) : Word :=
  if right then ⟨⟨c.num.signRight,c.num.mul.shifted⟩,c.den.mul.shifted⟩
  else ⟨⟨c.num.signLeft,c.num.mul.factor⟩,c.den.mul.factor⟩

def mulSetInput (right : Bool) (c : BinaryRationalArithmeticMultiplier.State) (w : Word) :
    BinaryRationalArithmeticMultiplier.State :=
  if right then
    {c with num := {c.num with signRight := w.numerator.negative, mul := {c.num.mul with shifted := w.numerator.magnitude}}, den := {c.den with mul := {c.den.mul with shifted := w.denominator}}}
  else
    {c with num := {c.num with signLeft := w.numerator.negative, mul := {c.num.mul with factor := w.numerator.magnitude}}, den := {c.den with mul := {c.den.mul with factor := w.denominator}}}

def mulSetOutput (c : BinaryRationalArithmeticMultiplier.State) (n d : List Bool) :
    BinaryRationalArithmeticMultiplier.State :=
  {c with norm := {c.norm with num := {c.norm.num with quot := {c.norm.num.quot with out := n}}, den := {c.norm.den with quot := {c.norm.den.quot with out := d}}}}

def multiplication : Layout where
  Core := BinaryRationalArithmeticMultiplier.State
  initial := BinaryRationalArithmeticMultiplier.initial
  step := BinaryRationalArithmeticMultiplier.step
  halted := fun c => decide (c.phase = .halt)
  trace := BinaryRationalArithmeticMultiplier.transitionTrace
  input := mulInput
  setInput := mulSetInput
  output := BinaryRationalArithmeticMultiplier.output
  setOutput := mulSetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by
    intro c h
    have hh : c.phase = .halt := by simpa only [decide_eq_true_eq] using h
    simp [BinaryRationalArithmeticMultiplier.step, hh]
  trace_active := by
    intro c h
    have hh : c.phase ≠ .halt := by
      intro he
      exact h (by simp [he])
    cases hp : c.phase <;> simp_all [BinaryRationalArithmeticMultiplier.transitionTrace]
    all_goals split <;> simp_all
  trace_bound := by
    intro c
    have h := BinaryRationalArithmeticMultiplier.transition_length c
    omega

theorem multiplication_advance (n : ℕ) (c : BinaryRationalArithmeticMultiplier.State) :
    multiplication.advance n c = BinaryRationalArithmeticMultiplier.advance n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

theorem multiplication_bitSteps (n : ℕ) (c : BinaryRationalArithmeticMultiplier.State) :
    multiplication.bitSteps n c = BinaryRationalArithmeticMultiplier.bitSteps n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (BinaryRationalArithmeticMultiplier.transitionTrace c).length +
      multiplication.bitSteps n (BinaryRationalArithmeticMultiplier.step c) = _
    rw [ih]
    rfl

end IdentityTesting.BinaryInterpreterLayouts
