import IdentityTesting.BinarySignedWords

/-! In-place negation of a canonical signed binary word. Only the sign cell and
the magnitude's end marker are read; the magnitude stack is not transported. -/
namespace IdentityTesting.BinarySignedNegation
open BinaryArithmetic BinarySignedWords

def step (w : Word) : Word :=
  { w with negative := if w.magnitude = [] then false else xor w.negative true }

def transitionTrace : List BitOp := [.readCell, .branch, .xorGate, .writeCell]

theorem step_value (w : Word) : (step w).value = -w.value := by
  by_cases h : w.magnitude = []
  · simp [step, Word.value, h, value, signedValue]
  · cases hs : w.negative <;> simp [step, h, Word.value, signedValue, hs]

theorem step_length (w : Word) : (step w).magnitude.length = w.magnitude.length := rfl

theorem binary_signed_negation_machine (z : ℤ) :
    (step (encode z)).value = -z ∧
    (step (encode z)).magnitude = (-z).natAbs.bits ∧
    transitionTrace.length = 4 := by
  refine ⟨?_, ?_, rfl⟩
  · rw [step_value, encode_value]
  · simp [step, encode]

end IdentityTesting.BinarySignedNegation
