import IdentityTesting.RationalRootSearchEncoding
import IdentityTesting.RationalAllocationRoot

/-! Representation bounds for each call made by the executable allocation-root
algorithm, expressed in the original probability-vector/radius input length. -/

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

def rootInputLength {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) : ℕ := V q + L e

private theorem encoding_one : L 1 = 3 := by
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits]

private theorem encoding_four : L 4 = 5 := by
  have h : (4 : ℕ).size = 3 := by simpa using (Nat.size_pow (n := 2))
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

theorem allocationRoot_upper_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    L ((k + 1) / e ^ 2) ≤ 2 * rootInputLength q e + 5 := by
  have hk : k + 1 ≤ V q := by unfold rationalVectorEncodingLength; omega
  have hc := rational_natCast_encoding_le (k + 1)
  norm_num only [Nat.cast_add, Nat.cast_one] at hc
  have hp := rational_pow_encoding e 2
  have hd := rational_div_encoding_le (k + 1) (e ^ 2)
  unfold rootInputLength
  omega

theorem allocationRootTolerance_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ)
    (e U : ℚ) : L (allocationRootTolerance q e U) ≤
      4 * V q + 5 * L e + 4 * L U + 58 := by
  have hone := encoding_one
  have hfour := encoding_four
  have h100 := rationalEncodingLength_hundred
  have hsub := rational_sub_encoding 1 e
  have hs2 := rational_pow_encoding (1 - e) 2
  have hb := oracleAtomLower_encoding_le q
  have hb2 := rational_pow_encoding (oracleAtomLower q) 2
  have hn := rational_mul_encoding ((1 - e) ^ 2) (oracleAtomLower q ^ 2)
  have hU2 := rational_pow_encoding U 2
  have h4U := rational_mul_encoding 4 (U ^ 2)
  have hadd := rational_add_encoding 1 (4 * U ^ 2)
  have hd := rational_mul_encoding 100 (1 + 4 * U ^ 2)
  have hdiv := rational_div_encoding_le
    ((1 - e) ^ 2 * oracleAtomLower q ^ 2) (100 * (1 + 4 * U ^ 2))
  have hmul := rational_mul_encoding
    ((1 - e) ^ 2 * oracleAtomLower q ^ 2 / (100 * (1 + 4 * U ^ 2))) e
  unfold allocationRootTolerance
  omega

theorem allocationRoot_actualTolerance_encoding_le {k : ℕ}
    (q : Fin (k + 1) → ℚ) (e : ℚ) :
    L (allocationRootTolerance q e ((k + 1) / e ^ 2)) ≤ 13 * rootInputLength q e + 78 := by
  have h := allocationRootTolerance_encoding_le q e ((k + 1) / e ^ 2)
  have hU := allocationRoot_upper_encoding_le q e
  unfold rootInputLength at *
  omega

theorem allocationRoot_actualFuel_le {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    oracleDyadicPrecision ((k + 1) / e ^ 2 - (1 - e)) (1 - e) ≤
      10 * rootInputLength q e + 33 := by
  have hU := allocationRoot_upper_encoding_le q e
  have hL := rational_sub_encoding 1 e
  have hone := encoding_one
  have hdiff := rational_sub_encoding ((k + 1) / e ^ 2) (1 - e)
  have hf := oracleDyadicPrecision_encoding_le_total ((k + 1) / e ^ 2 - (1 - e)) (1 - e)
  unfold rootInputLength at *
  omega

def rationalAllocationRootWithTrace {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    (ℚ × ℚ) × List ℚ :=
  let U := (k + 1) / e ^ 2
  rootSearchWithTrace (fun t => allocationOracle q t (allocationRootTolerance q e U)) e
    (oracleDyadicPrecision (U - (1 - e)) (1 - e)) (1 - e) U

theorem rationalAllocationRootWithTrace_result {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    (rationalAllocationRootWithTrace q e).1 = rationalAllocationRootInterval q e := by
  unfold rationalAllocationRootWithTrace
  rw [rootSearchWithTrace_result]
  rfl

theorem rationalAllocationRootWithTrace_length {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    (rationalAllocationRootWithTrace q e).2.length ≤ 10 * rootInputLength q e + 33 := by
  exact (rootSearchWithTrace_length _ _ _ _ _).trans (allocationRoot_actualFuel_le q e)

theorem rationalAllocationRootWithTrace_encoding_le {k : ℕ}
    (q : Fin (k + 1) → ℚ) (e t : ℚ)
    (ht : t ∈ (rationalAllocationRootWithTrace q e).2) :
    L t ≤ 60 * rootInputLength q e + 203 := by
  have h := rootSearchWithTrace_encoding_le _ _ _ _ _ t ht
  have hL := rational_sub_encoding 1 e
  have hone := encoding_one
  have hU := allocationRoot_upper_encoding_le q e
  have hf := allocationRoot_actualFuel_le q e
  unfold rootInputLength at *
  omega

theorem rationalAllocationRoot_oracleInputLength_le {k : ℕ}
    (q : Fin (k + 1) → ℚ) (e t : ℚ)
    (ht : t ∈ (rationalAllocationRootWithTrace q e).2) :
    allocationOracleInputLength q t (allocationRootTolerance q e ((k + 1) / e ^ 2)) ≤
      74 * rootInputLength q e + 281 := by
  have ht' := rationalAllocationRootWithTrace_encoding_le q e t ht
  have hσ := allocationRoot_actualTolerance_encoding_le q e
  unfold allocationOracleInputLength rootInputLength at *
  omega

theorem rationalAllocationRootInterval_encoding_le {k : ℕ}
    (q : Fin (k + 1) → ℚ) (e : ℚ) :
    L (rationalAllocationRootInterval q e).1 ≤ 60 * rootInputLength q e + 216 ∧
      L (rationalAllocationRootInterval q e).2 ≤ 60 * rootInputLength q e + 216 := by
  have hL := rational_sub_encoding 1 e
  have hone := encoding_one
  have hU := allocationRoot_upper_encoding_le q e
  have hf := allocationRoot_actualFuel_le q e
  obtain ⟨hl, hu⟩ := rootSearch_output_encoding_le_numeric
    (fun t => allocationOracle q t (allocationRootTolerance q e ((k + 1) / e ^ 2))) e
    (oracleDyadicPrecision ((k + 1) / e ^ 2 - (1 - e)) (1 - e)) (1 - e) ((k + 1) / e ^ 2)
  unfold rationalAllocationRootInterval allocationRootIntervalOn rootBracket
  constructor <;> unfold rootInputLength at * <;> omega

end IdentityTesting.RationalComputation
