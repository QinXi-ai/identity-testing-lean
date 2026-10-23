import IdentityTesting.RationalAlgorithmTraceSearchBounds
import IdentityTesting.RationalAlgorithmTraceVectorBounds
import IdentityTesting.RationalAlgorithmTraceCodeSize
import IdentityTesting.RationalOracleResourceBounds

/-! The original allocation input instantiates the actual register search.
This module does not charge computation of its initial parameters or precision. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

def allocationOracleSearchInput {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : RationalRegisters :=
  oracleMachineState a t (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
    (oracleBetaLower a t) (oracleBetaUpper (a 0) t) (σ / (100 * ∑ i, a i)) (σ / 100) 0 0 0 0

theorem allocationOracleSearchProgram_result {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    oracleSearchProgramOutput ((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
      (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).1 = allocationOracle a t σ := by
  rw [allocationOracleSearchInput, oracleSearchProgram_result]
  rfl

theorem allocationOracleSearchProgram_calls {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    let S := allocationOracleInputLength a t σ
    ((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
      (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).2.length ≤
      (30 * S + 127) * (2 * (S * (693 * S + 3363)) + 30) := by
  dsimp only
  have h := oracleSearchProgram_calls (k + 1) (allocationInnerPrecision a t σ)
    (allocationOuterFuel a t σ) (allocationOracleSearchInput a t σ)
  have hn := allocationInnerPrecision_le a t σ
  have hf := allocationOuterFuel_le a t σ
  have hk : k + 1 ≤ allocationOracleInputLength a t σ := by
    unfold allocationOracleInputLength rationalVectorEncodingLength
    omega
  have hc : 21 * allocationInnerPrecision a t σ + 45 ≤
      693 * allocationOracleInputLength a t σ + 3363 := by omega
  have hm := Nat.mul_le_mul hk hc
  have hp := Nat.mul_le_mul (show allocationOuterFuel a t σ + 1 ≤
    30 * allocationOracleInputLength a t σ + 127 by omega)
    (show 2 * ((k + 1) * (21 * allocationInnerPrecision a t σ + 45)) + 30 ≤
      2 * (allocationOracleInputLength a t σ *
        (693 * allocationOracleInputLength a t σ + 3363)) + 30 by omega)
  exact h.trans hp

theorem allocationOracleVectorProgram_operand_encoding {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ β : ℚ) (hβ : β ∈ (allocationOracleWithTrace a t σ).2)
    (objective : Bool) (c : RationalCall)
    (hc : c ∈ ((oracleVectorProgram objective (k + 1) (allocationInnerPrecision a t σ)).run
      (oracleProgramInput a t β (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)))).2) :
    let S := allocationOracleInputLength a t σ
    L c.lhs ≤ 1000000 * (S + 1) * (227 * S + 956) ∧
      L c.rhs ≤ 1000000 * (S + 1) * (227 * S + 956) := by
  dsimp only
  have h := oracleVectorProgram_operand_encoding a β t
    (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
    (allocationInnerPrecision a t σ) objective c hc
  have hn := allocationInnerPrecision_le a t σ
  have hb := allocationOracleWithTrace_encoding_le a t σ β hβ
  have hρ := allocationOraclePole_encoding_le a t
  have hk : k + 1 ≤ allocationOracleInputLength a t σ := by
    unfold allocationOracleInputLength rationalVectorEncodingLength
    omega
  have hs : oracleTraceSize a β t (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
      (allocationInnerPrecision a t σ) ≤ 227 * allocationOracleInputLength a t σ + 956 := by
    unfold oracleTraceSize allocationOracleInputLength at *
    omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 1000000 (Nat.add_le_add_right hk 1)) hs
  exact ⟨h.1.trans hm, h.2.trans hm⟩

end IdentityTesting.RationalComputation
