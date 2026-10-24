import IdentityTesting.RationalOracleInitializerExpressions
import IdentityTesting.RationalExpressionSequenceProjection

/-! Actual initialization from raw `[t, σ] ++ a` and a zero scratch region.
The output block contains the complete search state and computed counters. -/
namespace IdentityTesting.RationalComputation

def oracleInitializerProgram (k : ℕ) : RationalControlProgram :=
  rationalPrepareExpressions (oracleInitializerExpressions k) (k + 3)

def oracleInitializerInput {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : RationalRegisters :=
  oraclePreparationInput a t σ (List.replicate (rationalPreparationWork (oracleInitializerExpressions k)) 0)

theorem oracleInitializerInput_length {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (oracleInitializerInput a t σ).length = k + 3 + rationalPreparationWork (oracleInitializerExpressions k) := by
  simp [oracleInitializerInput, oraclePreparationInput]
  omega

theorem oracleInitializerProgram_block {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    ((((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1).drop (k + 3)).take (k + 28) =
      allocationOracleSearchInput a t σ ++
        [(allocationInnerPrecision a t σ : ℚ), (allocationOuterFuel a t σ : ℚ)] := by
  rw [RationalControlProgram.run_result]
  have h := rationalPrepareExpressions_block (oracleInitializerExpressions k) (k + 3) (k + 3)
    (oracleInitializerInput a t σ) (oracleInitializerInput a t σ) (Nat.le_refl _)
    (oracleInitializerExpressions_inputs k) (fun _ _ => rfl) (by rw [oracleInitializerInput_length])
  rw [oracleInitializerExpressions_length] at h
  exact h.trans (oracleInitializerExpressions_values a t σ _)

theorem oracleInitializerProgram_suffix {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1).drop (k + 3) =
      (allocationOracleSearchInput a t σ ++
        [(allocationInnerPrecision a t σ : ℚ), (allocationOuterFuel a t σ : ℚ)]) ++
        ((((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1).drop (k + 3)).drop (k + 28) := by
  rw [← oracleInitializerProgram_block a t σ]
  exact (List.take_append_drop _ _).symm

theorem oracleInitializerProgram_preserves_input {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (i : ℕ) (hi : i < k + 3) :
    (RationalOperand.reg i).read (((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1) =
      (RationalOperand.reg i).read (oracleInitializerInput a t σ) := by
  rw [RationalControlProgram.run_result]
  exact (rationalPrepareExpressions_correct (oracleInitializerExpressions k) (k + 3) (k + 3)
    (oracleInitializerInput a t σ) (oracleInitializerInput a t σ) (Nat.le_refl _)
    (oracleInitializerExpressions_inputs k) (fun _ _ => rfl)
    (by rw [oracleInitializerInput_length])).1 i hi

end IdentityTesting.RationalComputation
