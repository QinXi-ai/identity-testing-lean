import IdentityTesting.BinaryInterpreterArithmeticBound
import IdentityTesting.BinaryWorkspaceRationalCeilSize

/-! Ceiling-size is a separate control operation. It reuses the shared
load/store interpreter; a second physical input word is retained for that
interface, and is included in subsequent storage accounting. -/
namespace IdentityTesting.BinaryInterpreterCeilSize
open BinaryInterpreterLayout

structure Core where
  machine : BinaryRationalArithmeticCeilSize.State
  auxiliary : Word

def input (right : Bool) (c : Core) : Word :=
  if right then c.auxiliary else
    ⟨⟨c.machine.negative, c.machine.div.source⟩, c.machine.div.divisor⟩

def setInput (right : Bool) (c : Core) (w : Word) : Core :=
  if right then {c with auxiliary := w} else
    {c with machine := {c.machine with negative := w.numerator.negative, div := {c.machine.div with source := w.numerator.magnitude, divisor := w.denominator}}}

def setOutput (c : Core) (n d : List Bool) : Core :=
  {c with machine := {c.machine with denominator := d, measure := {c.machine.measure with norm := {c.machine.measure.norm with out := n}}}}

def layout : Layout where
  Core := Core
  initial := fun x y => ⟨BinaryRationalArithmeticCeilSize.initial x, y⟩
  step := fun c => {c with machine := BinaryRationalArithmeticCeilSize.step c.machine}
  halted := fun c => decide (c.machine.phase = .halt)
  trace := fun c => BinaryRationalArithmeticCeilSize.transitionTrace c.machine
  input := input
  setInput := setInput
  output := fun c => BinaryRationalArithmeticCeilSize.output c.machine
  setOutput := setOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by
    intro c h
    have hh : c.machine.phase = .halt := of_decide_eq_true h
    simp only [BinaryRationalArithmeticCeilSize.step, hh]
  trace_active := by
    intro c h
    have hh : c.machine.phase ≠ .halt := by
      intro he
      apply h
      exact decide_eq_true he
    cases hp : c.machine.phase <;>
      simp only [BinaryRationalArithmeticCeilSize.transitionTrace, hp]
    all_goals (repeat' first | split | simp_all | omega)
  trace_bound := by
    intro c
    exact (BinaryRationalArithmeticCeilSize.transition_length c.machine).trans (by omega)

theorem advance_eq (n : ℕ) (c : Core) :
    layout.advance n c = ⟨BinaryRationalArithmeticCeilSize.advance n c.machine, c.auxiliary⟩ := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simpa only [Layout.advance, layout, BinaryRationalArithmeticCeilSize.advance] using
        ih ⟨BinaryRationalArithmeticCeilSize.step c.machine, c.auxiliary⟩

theorem bitSteps_eq (n : ℕ) (c : Core) :
    layout.bitSteps n c = BinaryRationalArithmeticCeilSize.bitSteps n c.machine := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      simpa only [Layout.bitSteps, layout, BinaryRationalArithmeticCeilSize.bitSteps] using
        congrArg (fun t => (BinaryRationalArithmeticCeilSize.transitionTrace c.machine).length + t)
          (ih ⟨BinaryRationalArithmeticCeilSize.step c.machine, c.auxiliary⟩)

theorem local_run (p q : ℚ) :
    ∃ n,
      let c := layout.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      layout.halted (layout.advance n c) = true ∧
      layout.output (layout.advance n c) = BinaryRationalArithmetic.encode ((Nat.ceil p).size : ℚ) ∧
      layout.bitSteps n c ≤ 8000 * (RationalComputation.rationalEncodingLength p + 1)^2 := by
  obtain ⟨n, hh, ho, hc⟩ := BinaryRationalArithmeticCeilSize.binary_rational_ceilSize_machine p
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [advance_eq]
    exact decide_eq_true hh
  · rw [advance_eq]
    exact ho
  · rw [bitSteps_eq]
    exact hc

end IdentityTesting.BinaryInterpreterCeilSize
