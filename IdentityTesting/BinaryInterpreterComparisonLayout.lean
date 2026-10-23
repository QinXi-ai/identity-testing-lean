import IdentityTesting.BinaryInterpreterSubtractionLayout
import IdentityTesting.BinaryRationalArithmeticComparison

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

def cmpInput (right : Bool) (c : BinaryRationalArithmeticComparison.State) : Word := subInput right c.core
def cmpSetInput (right : Bool) (c : BinaryRationalArithmeticComparison.State) (w : Word) :
    BinaryRationalArithmeticComparison.State := {c with core := subSetInput right c.core w}
def cmpSetOutput (c : BinaryRationalArithmeticComparison.State) (n d : List Bool) :
    BinaryRationalArithmeticComparison.State := {c with numerator := n, denominator := d}

def comparison : Layout where
  Core := BinaryRationalArithmeticComparison.State
  initial := BinaryRationalArithmeticComparison.initial
  step := BinaryRationalArithmeticComparison.step
  halted := fun c => decide (c.phase = .halt)
  trace := BinaryRationalArithmeticComparison.transitionTrace
  input := cmpInput
  setInput := cmpSetInput
  output := BinaryRationalArithmeticComparison.output
  setOutput := cmpSetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by
    intro c h
    have hh : c.phase = .halt := by simpa only [decide_eq_true_eq] using h
    simp [BinaryRationalArithmeticComparison.step,hh]
  trace_active := by
    intro c h
    have hh : c.phase ≠ .halt := by intro he; exact h (by simp [he])
    cases hp : c.phase <;> simp_all [BinaryRationalArithmeticComparison.transitionTrace]
    all_goals split <;> simp_all
  trace_bound := by
    intro c
    have h := sub_trace_length c.core
    cases hp : c.phase <;> simp only [BinaryRationalArithmeticComparison.transitionTrace,hp]
    all_goals (repeat' first | split | simp_all | omega)

theorem comparison_advance (n : ℕ) (c : BinaryRationalArithmeticComparison.State) :
    comparison.advance n c = BinaryRationalArithmeticComparison.advance n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

theorem comparison_bitSteps (n : ℕ) (c : BinaryRationalArithmeticComparison.State) :
    comparison.bitSteps n c = BinaryRationalArithmeticComparison.bitSteps n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (BinaryRationalArithmeticComparison.transitionTrace c).length +
      comparison.bitSteps n (BinaryRationalArithmeticComparison.step c) = _
    rw [ih]
    rfl

end IdentityTesting.BinaryInterpreterLayouts
