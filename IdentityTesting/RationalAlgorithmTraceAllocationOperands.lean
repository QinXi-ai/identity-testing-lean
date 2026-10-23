import IdentityTesting.RationalAlgorithmTraceSearchOperands
import IdentityTesting.RationalAlgorithmTraceAllocationSearch

/-! The original allocation input controls every operand of its actual search
run; charging its initial parameter computation is a separate obligation. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem allocationOracleSearchTraceSize_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    oracleSearchTraceSize a t (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
      (σ / (100 * ∑ i, a i)) (σ / 100) (oracleBetaLower a t) (oracleBetaUpper (a 0) t)
      (allocationInnerPrecision a t σ) (allocationOuterFuel a t σ) ≤
      500 * allocationOracleInputLength a t σ + 2500 := by
  have hn := allocationInnerPrecision_le a t σ
  have hf := allocationOuterFuel_le a t σ
  have hb := oracleBetaLower_encoding_le a t
  have hB := oracleBetaUpper_encoding_le (a 0) t
  have ha := rational_entry_encoding_le a 0
  have hρ := allocationOraclePole_encoding_le a t
  have hζ := allocationOracleTolerance_encoding_le a σ
  have hmargin := rational_div_encoding_le σ 100
  have h100 := rational_natCast_encoding_le 100
  norm_num only [Nat.cast_ofNat] at h100
  unfold oracleSearchTraceSize allocationOracleInputLength at *
  omega

theorem allocationOracleSearchProgram_operand_encoding {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (c : RationalCall)
    (hc : c ∈ ((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
      (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).2) :
    let S := allocationOracleInputLength a t σ
    L c.lhs ≤ 20000000 * (S + 1) * (500 * S + 2500) ∧
      L c.rhs ≤ 20000000 * (S + 1) * (500 * S + 2500) := by
  dsimp only
  have h := oracleSearchProgram_operand_encoding (allocationInnerPrecision a t σ)
    (allocationOuterFuel a t σ) a t
    (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
    (σ / (100 * ∑ i, a i)) (σ / 100) (oracleBetaLower a t) (oracleBetaUpper (a 0) t) c hc
  have hs := allocationOracleSearchTraceSize_le a t σ
  have hk : k + 1 ≤ allocationOracleInputLength a t σ := by
    unfold allocationOracleInputLength rationalVectorEncodingLength
    omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 20000000 (Nat.add_le_add_right hk 1)) hs
  exact ⟨h.1.trans hm, h.2.trans hm⟩

end IdentityTesting.RationalComputation
