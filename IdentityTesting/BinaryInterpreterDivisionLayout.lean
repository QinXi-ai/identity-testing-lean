import IdentityTesting.BinaryInterpreterMultiplicationLayout
import IdentityTesting.BinaryRationalArithmeticDividerBound

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

def divInput (right : Bool) (c : BinaryRationalArithmeticDivider.State) : Word :=
  if right then BinaryRationalArithmeticDivider.reciprocalLayout (mulInput true c.core)
  else mulInput false c.core

def divSetInput (right : Bool) (c : BinaryRationalArithmeticDivider.State) (w : Word) :
    BinaryRationalArithmeticDivider.State :=
  {c with core := mulSetInput right c.core (if right then BinaryRationalArithmeticDivider.reciprocalLayout w else w)}

def divSetOutput (c : BinaryRationalArithmeticDivider.State) (n d : List Bool) :
    BinaryRationalArithmeticDivider.State :=
  if c.phase = .zeroHalt then
    {c with core := {c.core with den := {c.core.den with mul := {c.core.den.mul with shifted := n}}}, zeroDen := d}
  else {c with core := mulSetOutput c.core n d}

def division : Layout where
  Core := BinaryRationalArithmeticDivider.State
  initial := BinaryRationalArithmeticDivider.initial
  step := BinaryRationalArithmeticDivider.step
  halted := fun c => decide (c.phase = .halt ∨ c.phase = .zeroHalt)
  trace := BinaryRationalArithmeticDivider.transitionTrace
  input := divInput
  setInput := divSetInput
  output := BinaryRationalArithmeticDivider.output
  setOutput := divSetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by
    intro c n d
    by_cases h : c.phase = .zeroHalt <;>
      simp [divSetOutput,h,BinaryRationalArithmeticDivider.output,mulSetOutput,BinaryRationalArithmeticMultiplier.output]
  output_den_set := by
    intro c n d
    by_cases h : c.phase = .zeroHalt <;>
      simp [divSetOutput,h,BinaryRationalArithmeticDivider.output,mulSetOutput,BinaryRationalArithmeticMultiplier.output]
  setOutput_self := by
    intro c
    cases c with
    | mk phase core zeroDen => cases phase <;> rfl
  setOutput_set := by
    intro c n d n' d'
    by_cases h : c.phase = .zeroHalt <;> simp [divSetOutput,h,mulSetOutput]
  step_halt := by
    intro c h
    have hh : c.phase = .halt ∨ c.phase = .zeroHalt := by simpa only [decide_eq_true_eq] using h
    rcases hh with hh | hh <;> simp [BinaryRationalArithmeticDivider.step,hh]
  trace_active := by
    intro c h
    have hh : ¬ (c.phase = .halt ∨ c.phase = .zeroHalt) := by intro he; exact h (by simp [he])
    cases hp : c.phase <;> simp_all [BinaryRationalArithmeticDivider.transitionTrace]
    all_goals split <;> simp_all
  trace_bound := by
    intro c
    have h := BinaryRationalArithmeticMultiplier.transition_length c.core
    cases hp : c.phase <;> simp only [BinaryRationalArithmeticDivider.transitionTrace,hp]
    all_goals (repeat' first | split | simp_all | omega)

theorem division_advance (n : ℕ) (c : BinaryRationalArithmeticDivider.State) :
    division.advance n c = BinaryRationalArithmeticDivider.advance n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

theorem division_bitSteps (n : ℕ) (c : BinaryRationalArithmeticDivider.State) :
    division.bitSteps n c = BinaryRationalArithmeticDivider.bitSteps n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (BinaryRationalArithmeticDivider.transitionTrace c).length +
      division.bitSteps n (BinaryRationalArithmeticDivider.step c) = _
    rw [ih]
    rfl

end IdentityTesting.BinaryInterpreterLayouts
