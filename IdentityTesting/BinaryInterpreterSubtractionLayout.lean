import IdentityTesting.BinaryInterpreterAdditionLayout
import IdentityTesting.BinaryRationalArithmeticSubtractor

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

def subInput (right : Bool) (c : BinaryRationalArithmeticSubtractor.State) : Word := addInput right c.core
def subSetInput (right : Bool) (c : BinaryRationalArithmeticSubtractor.State) (w : Word) :
    BinaryRationalArithmeticSubtractor.State := {c with core := addSetInput right c.core w}
def subSetOutput (c : BinaryRationalArithmeticSubtractor.State) (n d : List Bool) :
    BinaryRationalArithmeticSubtractor.State := {c with core := addSetOutput c.core n d}

theorem sub_trace_length (c : BinaryRationalArithmeticSubtractor.State) :
    (BinaryRationalArithmeticSubtractor.transitionTrace c).length ≤ 14 := by
  have h := BinaryRationalArithmeticAdder.transition_length c.core
  cases hp : c.phase <;> simp only [BinaryRationalArithmeticSubtractor.transitionTrace,hp]
  all_goals (repeat' first | split | simp_all | omega)

def subtraction : Layout where
  Core := BinaryRationalArithmeticSubtractor.State
  initial := BinaryRationalArithmeticSubtractor.initial
  step := BinaryRationalArithmeticSubtractor.step
  halted := fun c => decide (c.phase = .halt)
  trace := BinaryRationalArithmeticSubtractor.transitionTrace
  input := subInput
  setInput := subSetInput
  output := BinaryRationalArithmeticSubtractor.output
  setOutput := subSetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by
    intro c h
    have hh : c.phase = .halt := by simpa only [decide_eq_true_eq] using h
    simp [BinaryRationalArithmeticSubtractor.step, hh]
  trace_active := by
    intro c h
    have hh : c.phase ≠ .halt := by intro he; exact h (by simp [he])
    cases hp : c.phase <;> simp_all [BinaryRationalArithmeticSubtractor.transitionTrace]
    all_goals split <;> simp_all
  trace_bound := by intro c; have h := sub_trace_length c; omega

theorem subtraction_advance (n : ℕ) (c : BinaryRationalArithmeticSubtractor.State) :
    subtraction.advance n c = BinaryRationalArithmeticSubtractor.advance n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

theorem subtraction_bitSteps (n : ℕ) (c : BinaryRationalArithmeticSubtractor.State) :
    subtraction.bitSteps n c = BinaryRationalArithmeticSubtractor.bitSteps n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (BinaryRationalArithmeticSubtractor.transitionTrace c).length +
      subtraction.bitSteps n (BinaryRationalArithmeticSubtractor.step c) = _
    rw [ih]
    rfl

end IdentityTesting.BinaryInterpreterLayouts
