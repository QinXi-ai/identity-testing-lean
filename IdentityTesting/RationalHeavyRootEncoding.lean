import IdentityTesting.RationalAllocationRootEncoding
import IdentityTesting.HeavyRootOracle

/-! Original-input representation bounds for the actual heavy-root search. -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

private theorem encoding_one : L 1 = 3 := by
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits]

private theorem encoding_thousand : L 1000 = 12 := by
  have h : (1000 : ℕ).size = 10 := by
    have hle : (1000 : ℕ).size ≤ 10 := Nat.size_le.mpr (by norm_num)
    have hgt : 9 < (1000 : ℕ).size := Nat.lt_size.mpr (by norm_num)
    omega
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

theorem heavyOracleLower_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    L (heavyOracleLower a e) ≤ 2 * rootInputLength a e + 6 := by
  have hr := rational_vector_sum_encoding a
  have he := rational_pow_encoding e 2
  have hd := rational_div_encoding_le (∑ i, a i) (e ^ 2)
  unfold heavyOracleLower rootInputLength
  omega

theorem heavyOracleUpper_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    L (heavyOracleUpper a e) ≤ 4 * rootInputLength a e + 15 := by
  have hk : k + 1 ≤ V a := by unfold rationalVectorEncodingLength; omega
  have hn := rational_natCast_encoding_le (k + 2)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hn
  have hn2 := rational_pow_encoding (k + 2) 2
  have hr := rational_vector_sum_encoding a
  have he := rational_pow_encoding e 2
  have hm := rational_mul_encoding ((k + 2) ^ 2) (∑ i, a i)
  have hd := rational_div_encoding_le ((k + 2) ^ 2 * ∑ i, a i) (e ^ 2)
  unfold heavyOracleUpper rootInputLength
  omega

theorem heavyOracleTolerance_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    L (heavyOracleTolerance a e) ≤ 6 * rootInputLength a e + 30 := by
  have hU := heavyOracleUpper_encoding_le a e
  have hr := rational_vector_sum_encoding a
  have hd := rational_div_encoding_le (∑ i, a i) (heavyOracleUpper a e)
  have hm := rational_min_encoding 1 ((∑ i, a i) / heavyOracleUpper a e)
  have hdiv := rational_div_encoding_le (min 1 ((∑ i, a i) / heavyOracleUpper a e)) 1000
  have hone := encoding_one
  have hc := encoding_thousand
  unfold heavyOracleTolerance rootInputLength at *
  omega

theorem heavyRoot_actualFuel_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    oracleDyadicPrecision (heavyOracleUpper a e - heavyOracleLower a e)
      (heavyOracleLower a e) ≤ 14 * rootInputLength a e + 50 := by
  have hL := heavyOracleLower_encoding_le a e
  have hU := heavyOracleUpper_encoding_le a e
  have hd := rational_sub_encoding (heavyOracleUpper a e) (heavyOracleLower a e)
  have hf := oracleDyadicPrecision_encoding_le_total
    (heavyOracleUpper a e - heavyOracleLower a e) (heavyOracleLower a e)
  omega

def heavyRootOracleWithTrace {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    (ℚ × ℚ) × List ℚ :=
  rootSearchWithTrace (fun t => heavyValueOracle a t (heavyOracleTolerance a e)) e
    (oracleDyadicPrecision (heavyOracleUpper a e - heavyOracleLower a e)
      (heavyOracleLower a e)) (heavyOracleLower a e) (heavyOracleUpper a e)

theorem heavyRootOracleWithTrace_result {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    (heavyRootOracleWithTrace a e).1 = heavyRootOracle a e := by
  unfold heavyRootOracleWithTrace
  rw [rootSearchWithTrace_result]
  rfl

theorem heavyRootOracleWithTrace_length {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    (heavyRootOracleWithTrace a e).2.length ≤ 14 * rootInputLength a e + 50 := by
  exact (rootSearchWithTrace_length _ _ _ _ _).trans (heavyRoot_actualFuel_le a e)

theorem heavyRootOracleWithTrace_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e t : ℚ)
    (ht : t ∈ (heavyRootOracleWithTrace a e).2) :
    L t ≤ 84 * rootInputLength a e + 305 := by
  have h := rootSearchWithTrace_encoding_le _ _ _ _ _ t ht
  have hL := heavyOracleLower_encoding_le a e
  have hU := heavyOracleUpper_encoding_le a e
  have hf := heavyRoot_actualFuel_le a e
  omega

theorem heavyRootOracle_oracleInputLength_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e t : ℚ)
    (ht : t ∈ (heavyRootOracleWithTrace a e).2) :
    allocationOracleInputLength a t (heavyOracleTolerance a e) ≤
      91 * rootInputLength a e + 335 := by
  have ht' := heavyRootOracleWithTrace_encoding_le a e t ht
  have hσ := heavyOracleTolerance_encoding_le a e
  unfold allocationOracleInputLength rootInputLength at *
  omega

theorem heavyRootOracle_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) :
    L (heavyRootOracle a e).1 ≤ 84 * rootInputLength a e + 318 ∧
      L (heavyRootOracle a e).2 ≤ 84 * rootInputLength a e + 318 := by
  have hL := heavyOracleLower_encoding_le a e
  have hU := heavyOracleUpper_encoding_le a e
  have hf := heavyRoot_actualFuel_le a e
  obtain ⟨hl, hu⟩ := rootSearch_output_encoding_le_numeric
    (fun t => heavyValueOracle a t (heavyOracleTolerance a e)) e
    (oracleDyadicPrecision (heavyOracleUpper a e - heavyOracleLower a e) (heavyOracleLower a e))
    (heavyOracleLower a e) (heavyOracleUpper a e)
  unfold heavyRootOracle rootBracket
  constructor <;> omega

end IdentityTesting.RationalComputation
