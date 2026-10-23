import IdentityTesting.BinaryInterpreterCopyRuns

/-! Structural interface for an existing arithmetic machine. Its laws concern
only finite control, physical input/output stack views, and setters. No desired
arithmetic result or execution-time theorem is an interface field. Concrete
instances supply their previously proved local arithmetic run separately. -/
namespace IdentityTesting.BinaryInterpreterLayout

abbrev Word := BinaryRationalArithmetic.Word

structure Layout where
  Core : Type
  initial : Word → Word → Core
  step : Core → Core
  halted : Core → Bool
  trace : Core → List BinaryArithmetic.BitOp
  input : Bool → Core → Word
  setInput : Bool → Core → Word → Core
  output : Core → Word
  setOutput : Core → List Bool → List Bool → Core
  input_initial : ∀ (right : Bool) (x y : Word), input right (initial x y) = if right then y else x
  setInput_initial : ∀ (right : Bool) (x y w : Word),
    setInput right (initial x y) w = if right then initial x w else initial w y
  output_num_set : ∀ c n d, (output (setOutput c n d)).numerator.magnitude = n
  output_den_set : ∀ c n d, (output (setOutput c n d)).denominator = d
  setOutput_self : ∀ c, setOutput c (output c).numerator.magnitude (output c).denominator = c
  setOutput_set : ∀ c n d n' d', setOutput (setOutput c n d) n' d' = setOutput c n' d'
  step_halt : ∀ c, halted c = true → step c = c
  trace_active : ∀ c, halted c ≠ true → 1 ≤ (trace c).length
  trace_bound : ∀ c, (trace c).length ≤ 31

namespace Layout

def advance (L : Layout) : ℕ → L.Core → L.Core
  | 0, c => c
  | n+1, c => advance L n (L.step c)

def bitSteps (L : Layout) : ℕ → L.Core → ℕ
  | 0, _ => 0
  | n+1, c => (L.trace c).length + bitSteps L n (L.step c)

theorem advance_halt (L : Layout) (n : ℕ) (c : L.Core) (h : L.halted c = true) :
    L.advance n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [advance, L.step_halt c h] using ih

end Layout
end IdentityTesting.BinaryInterpreterLayout
