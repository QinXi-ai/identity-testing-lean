import IdentityTesting.RationalAlgorithmTraceCoordinateBounds
import IdentityTesting.RationalOracleResourceBounds

/-! Actual allocation-oracle inputs instantiate the register-program bounds.
Computing the precision and scheduling the full oracle remain separate stages. -/
namespace IdentityTesting.RationalComputation

theorem allocationOracle_coordinate_program_calls {k : ℕ}
    (a : Fin (k + 1) → ℚ) (t σ β : ℚ) (j : Fin (k + 1)) :
    ((coordinateProgram (allocationInnerPrecision a t σ)).run
      (coordinateRegisters (a j) β 0 1)).2.length ≤
        693 * allocationOracleInputLength a t σ + 3318 := by
  have h := coordinateProgram_calls (a j) β (allocationInnerPrecision a t σ)
  have hn := allocationInnerPrecision_le a t σ
  omega

theorem allocationOracle_coordinate_program_operands {k : ℕ}
    (a : Fin (k + 1) → ℚ) (t σ β : ℚ)
    (hβ : β ∈ (allocationOracleWithTrace a t σ).2) (j : Fin (k + 1))
    (c : RationalCall) (hc : c ∈ ((coordinateProgram (allocationInnerPrecision a t σ)).run
      (coordinateRegisters (a j) β 0 1)).2) :
    rationalEncodingLength c.lhs ≤ 2870 * allocationOracleInputLength a t σ + 13737 ∧
    rationalEncodingLength c.rhs ≤ 2870 * allocationOracleInputLength a t σ + 13737 := by
  have h := coordinateProgram_operand_encoding (a j) β (allocationInnerPrecision a t σ) c hc
  have hn := allocationInnerPrecision_le a t σ
  have hb := allocationOracleWithTrace_encoding_le a t σ β hβ
  have ha := rational_entry_encoding_le a j
  unfold allocationOracleInputLength at *
  constructor <;> omega

end IdentityTesting.RationalComputation
