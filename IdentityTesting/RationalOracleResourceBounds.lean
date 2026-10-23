import IdentityTesting.RationalOracleOutputEncoding
import IdentityTesting.RationalOracleSearchTrace

/-! Bounds on the representations passed through the actual oracle. These
bounds do not assert a running time for rational arithmetic. -/

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem allocationOracleBudget_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ β : ℚ) :
    let S := allocationOracleInputLength a t σ
    let ρ := oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
    let I := oracleBudgetInterval a t β ρ (allocationInnerPrecision a t σ)
    L I.1 ≤ 2212 * S ^ 2 + 10680 * S + 3 ∧
      L I.2 ≤ 2212 * S ^ 2 + 10680 * S + 3 := by
  dsimp only
  let S := allocationOracleInputLength a t σ
  have hn := allocationInnerPrecision_le a t σ
  have hρ := allocationOraclePole_encoding_le a t
  have hV : V a ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have hT : L t + V a ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have hk : k + 1 ≤ S := by
    have h : k + 1 ≤ V a := by unfold rationalVectorEncodingLength; omega
    omega
  have hb : 2 * L t + 24 * allocationInnerPrecision a t σ +
      24 * L (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)) + 106 ≤
      1106 * S + 5338 := by omega
  have hmul := Nat.mul_le_mul hk hb
  obtain ⟨hl, hu⟩ := oracleBudgetInterval_encoding_le a t β
    (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
    (allocationInnerPrecision a t σ)
  constructor <;> dsimp only [S] at * <;> nlinarith

theorem allocationOracle_coordinate_polynomial_encoding_le {k : ℕ}
    (a : Fin (k + 1) → ℚ) (t σ β : ℚ)
    (hβ : β ∈ (allocationOracleWithTrace a t σ).2)
    (j : Fin (k + 1)) (i : ℕ) (hi : i < allocationInnerPrecision a t σ) :
    L (coordinatePolynomial (a j) β (coordinateQuery (a j) β i)) ≤
      2870 * allocationOracleInputLength a t σ + 13737 := by
  have hn := allocationInnerPrecision_le a t σ
  have hb := allocationOracleWithTrace_encoding_le a t σ β hβ
  have ha : L (a j) ≤ V a := by
    have hs := Finset.single_le_sum (f := fun j => L (a j))
      (fun j _ => Nat.zero_le (L (a j))) (Finset.mem_univ j)
    dsimp only at hs
    unfold rationalVectorEncodingLength
    omega
  have hV : V a ≤ allocationOracleInputLength a t σ := by
    unfold allocationOracleInputLength
    omega
  have hp := coordinateQuery_polynomial_encoding_le (a j) β i
  omega

end IdentityTesting.RationalComputation
