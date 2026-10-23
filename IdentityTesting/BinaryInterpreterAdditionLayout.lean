import IdentityTesting.BinaryInterpreterLayout
import IdentityTesting.BinaryRationalArithmeticAdderBound

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

def addInput (right : Bool) (c : BinaryRationalArithmeticAdder.State) : Word :=
  if right then ⟨⟨c.right.signLeft,c.right.mul.factor⟩,c.base.den.mul.shifted⟩
  else ⟨⟨c.base.num.signLeft,c.base.num.mul.factor⟩,c.base.den.mul.factor⟩

def addSetInput (right : Bool) (c : BinaryRationalArithmeticAdder.State) (w : Word) :
    BinaryRationalArithmeticAdder.State :=
  if right then
    {c with right := {c.right with signLeft := w.numerator.negative, mul := {c.right.mul with factor := w.numerator.magnitude}}, base := {c.base with den := {c.base.den with mul := {c.base.den.mul with shifted := w.denominator}}}}
  else
    {c with base := {c.base with num := {c.base.num with signLeft := w.numerator.negative, mul := {c.base.num.mul with factor := w.numerator.magnitude}}, den := {c.base.den with mul := {c.base.den.mul with factor := w.denominator}}}}

def addSetOutput (c : BinaryRationalArithmeticAdder.State) (n d : List Bool) :
    BinaryRationalArithmeticAdder.State :=
  {c with base := {c.base with norm := {c.base.norm with num := {c.base.norm.num with quot := {c.base.norm.num.quot with out := n}}, den := {c.base.norm.den with quot := {c.base.norm.den.quot with out := d}}}}}

def addition : Layout where
  Core := BinaryRationalArithmeticAdder.State
  initial := BinaryRationalArithmeticAdder.initial
  step := BinaryRationalArithmeticAdder.step
  halted := fun c => decide (c.phase = .halt)
  trace := BinaryRationalArithmeticAdder.transitionTrace
  input := addInput
  setInput := addSetInput
  output := BinaryRationalArithmeticAdder.output
  setOutput := addSetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by
    intro c h
    have hh : c.phase = .halt := by simpa only [decide_eq_true_eq] using h
    simp [BinaryRationalArithmeticAdder.step, hh]
  trace_active := by
    intro c h
    have hh : c.phase ≠ .halt := by
      intro he
      exact h (by simp [he])
    cases hp : c.phase <;> simp_all [BinaryRationalArithmeticAdder.transitionTrace]
    all_goals split <;> simp_all
  trace_bound := by
    intro c
    have h := BinaryRationalArithmeticAdder.transition_length c
    omega

theorem addition_advance (n : ℕ) (c : BinaryRationalArithmeticAdder.State) :
    addition.advance n c = BinaryRationalArithmeticAdder.advance n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

theorem addition_bitSteps (n : ℕ) (c : BinaryRationalArithmeticAdder.State) :
    addition.bitSteps n c = BinaryRationalArithmeticAdder.bitSteps n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (BinaryRationalArithmeticAdder.transitionTrace c).length +
      addition.bitSteps n (BinaryRationalArithmeticAdder.step c) = _
    rw [ih]
    rfl

end IdentityTesting.BinaryInterpreterLayouts
