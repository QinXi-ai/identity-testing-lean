import IdentityTesting.RationalOracleEvaluationEncoding
import IdentityTesting.RationalAllocationOracle

/-! Encoding bounds for the parameters and loop bounds computed from the
original allocation-oracle inputs. The final equality connects the bounded
precisions to the existing executable oracle. -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation

local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

private theorem encoding_one : L 1 = 3 := by
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits]

private theorem encoding_four : L 4 = 5 := by
  have h : (4 : ℕ).size = 3 := by simpa using (Nat.size_pow (n := 2))
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

theorem rationalEncodingLength_hundred : L 100 = 9 := by
  have h : (100 : ℕ).size = 7 := by
    have hle : (100 : ℕ).size ≤ 7 := Nat.size_le.mpr (by norm_num)
    have hgt : 6 < (100 : ℕ).size := Nat.lt_size.mpr (by norm_num)
    omega
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

private theorem encoding_128 : L 128 = 10 := by
  have h : (128 : ℕ).size = 8 := by simpa using (Nat.size_pow (n := 7))
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

private theorem encoding_half : L (1 / 2) = 4 := by
  have h : (2 : ℕ).size = 2 := by simpa using (Nat.size_pow (n := 1))
  rw [one_div, rational_inv_encoding 2 (by norm_num)]
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]

theorem rational_reciprocal_encoding (q : ℚ) : L (1 / q) = L q := by
  by_cases h : q = 0
  · subst q
    simp
  · simpa only [one_div] using rational_inv_encoding q h

theorem rational_min_encoding (p q : ℚ) : L (min p q) ≤ max (L p) (L q) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h]
    exact le_max_left _ _
  · rw [min_eq_right h]
    exact le_max_right _ _

theorem rational_natCast_encoding_le (k : ℕ) : L (k : ℚ) ≤ k + 2 := by
  have h : k.size ≤ k := Nat.size_le.mpr k.lt_two_pow_self
  simpa [rationalEncodingLength, numeratorBits, denominatorBits, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using Nat.add_le_add_right h 2

theorem rational_entry_encoding_le {k : ℕ} (a : Fin k → ℚ) (i : Fin k) : L (a i) ≤ V a := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
    Nat.zero_le (L (a j))) (Finset.mem_univ i)
  exact h.trans (Nat.le_add_left _ _)

theorem oracleDyadicPrecision_encoding_le_total (C δ : ℚ) :
    oracleDyadicPrecision C δ ≤ L C + L δ + 1 := by
  have hp := oracleDyadicPrecision_le C δ (numeratorBits (C / δ))
    (rational_lt_pow_numeratorBits (C / δ)).le
  have he := rational_div_encoding_le C δ
  have hn : numeratorBits (C / δ) ≤ L (C / δ) := by
    unfold rationalEncodingLength
    omega
  omega

theorem oracleAtomLower_encoding_le {k : ℕ} (a : Fin k → ℚ) :
    L (oracleAtomLower a) ≤ 2 * V a + 3 := by
  have h := rational_sum_encoding Finset.univ (fun i => 1 / a i)
  simp only [rational_reciprocal_encoding] at h
  rw [oracleAtomLower, rational_reciprocal_encoding]
  unfold rationalVectorEncodingLength
  omega

theorem oracleBetaLower_encoding_le {k : ℕ} (a : Fin k → ℚ) (t : ℚ) :
    L (oracleBetaLower a t) ≤ 2 * L t + 2 * V a + 6 := by
  have ht := rational_pow_encoding t 2
  have hr := rational_vector_sum_encoding a
  have hm := rational_mul_encoding (t ^ 2) (∑ i, a i)
  rw [oracleBetaLower, rational_reciprocal_encoding]
  omega

theorem oracleBetaUpper_encoding_le (a t : ℚ) :
    L (oracleBetaUpper a t) ≤ 12 * L t + 11 * L a + 47 := by
  have ht2 := rational_pow_encoding t 2
  have ht4 := rational_pow_encoding t 4
  have ha2 := rational_pow_encoding a 2
  have ha3 := rational_pow_encoding a 3
  have hm := rational_mul_encoding (t ^ 2) (a ^ 2)
  have hs := rational_add_encoding 1 (t ^ 2 * a ^ 2)
  have hn := rational_pow_encoding (1 + t ^ 2 * a ^ 2) 2
  have hd := rational_mul_encoding (t ^ 4) (a ^ 3)
  have hq := rational_div_encoding_le ((1 + t ^ 2 * a ^ 2) ^ 2) (t ^ 4 * a ^ 3)
  have hone := encoding_one
  unfold oracleBetaUpper
  omega

theorem oraclePoleGap_encoding_le (a B : ℚ) :
    L (oraclePoleGap a B) ≤ L a + L B + 10 := by
  have hm := rational_mul_encoding 128 B
  have hd := rational_div_encoding_le a (128 * B)
  have hh := rational_min_encoding (1 / 2) (a / (128 * B))
  have hc := encoding_128
  have hhalf := encoding_half
  unfold oraclePoleGap
  omega

theorem allocationOraclePole_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t : ℚ) :
    L (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)) ≤
      12 * L t + 13 * V a + 60 := by
  have h := oraclePoleGap_encoding_le (oracleAtomLower a) (oracleBetaUpper (a 0) t)
  have hl := oracleAtomLower_encoding_le a
  have hu := oracleBetaUpper_encoding_le (a 0) t
  have ha := rational_entry_encoding_le a 0
  omega

theorem allocationOracleCoefficient_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t : ℚ) :
    L (allocationOracleCoefficient a t) ≤ 26 * L t + 31 * V a + 142 := by
  let ρ := oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
  have hρ : L ρ ≤ 12 * L t + 13 * V a + 60 := allocationOraclePole_encoding_le a t
  have hk : k + 1 ≤ V a := by unfold rationalVectorEncodingLength; omega
  have hn := rational_natCast_encoding_le (k + 1)
  have ht := rational_pow_encoding t 2
  have hr := rational_vector_sum_encoding a
  have hr2 := rational_pow_encoding (∑ i, a i) 2
  have hρ2 := rational_pow_encoding ρ 2
  have h4 := encoding_four
  have hm1 := rational_mul_encoding 4 ((k + 1 : ℕ) : ℚ)
  have hm2 := rational_mul_encoding (4 * ((k + 1 : ℕ) : ℚ)) (t ^ 2)
  have hm3 := rational_mul_encoding (4 * ((k + 1 : ℕ) : ℚ) * t ^ 2) ((∑ i, a i) ^ 2)
  have hd := rational_div_encoding_le
    (4 * ((k + 1 : ℕ) : ℚ) * t ^ 2 * (∑ i, a i) ^ 2) (ρ ^ 2)
  change L (4 * (k + 1) * t ^ 2 * (∑ i, a i) ^ 2 / ρ ^ 2) ≤ _
  norm_num only [Nat.cast_add, Nat.cast_one] at hn hm1 hm2 hm3 hd
  omega

def allocationOracleInputLength {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℕ :=
  V a + L t + L σ

def allocationInnerPrecision {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℕ :=
  let ζ := σ / (100 * ∑ i, a i)
  oracleDyadicPrecision 1 (min ζ (ζ / allocationOracleCoefficient a t))

def allocationOuterFuel {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℕ :=
  oracleDyadicPrecision (oracleBetaUpper (a 0) t - oracleBetaLower a t)
    ((σ / (100 * ∑ i, a i)) * oracleBetaLower a t)

theorem allocationOracleTolerance_encoding_le {k : ℕ} (a : Fin k → ℚ) (σ : ℚ) :
    L (σ / (100 * ∑ i, a i)) ≤ L σ + 2 * V a + 12 := by
  have hr := rational_vector_sum_encoding a
  have hm := rational_mul_encoding 100 (∑ i, a i)
  have hd := rational_div_encoding_le σ (100 * ∑ i, a i)
  have hc := rationalEncodingLength_hundred
  omega

theorem allocationInnerPrecision_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    allocationInnerPrecision a t σ ≤ 33 * allocationOracleInputLength a t σ + 158 := by
  let ζ := σ / (100 * ∑ i, a i)
  let M := allocationOracleCoefficient a t
  have hζ : L ζ ≤ L σ + 2 * V a + 12 := allocationOracleTolerance_encoding_le a σ
  have hM : L M ≤ 26 * L t + 31 * V a + 142 := allocationOracleCoefficient_encoding_le a t
  have hd := rational_div_encoding_le ζ M
  have hm := rational_min_encoding ζ (ζ / M)
  have hp := oracleDyadicPrecision_encoding_le_total 1 (min ζ (ζ / M))
  have hone := encoding_one
  change oracleDyadicPrecision 1 (min ζ (ζ / M)) ≤ _
  unfold allocationOracleInputLength
  omega

theorem allocationOuterFuel_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    allocationOuterFuel a t σ ≤ 30 * allocationOracleInputLength a t σ + 126 := by
  let ζ := σ / (100 * ∑ i, a i)
  let b := oracleBetaLower a t
  let B := oracleBetaUpper (a 0) t
  have hζ : L ζ ≤ L σ + 2 * V a + 12 := allocationOracleTolerance_encoding_le a σ
  have hb : L b ≤ 2 * L t + 2 * V a + 6 := oracleBetaLower_encoding_le a t
  have hB : L B ≤ 12 * L t + 11 * L (a 0) + 47 := oracleBetaUpper_encoding_le (a 0) t
  have ha := rational_entry_encoding_le a 0
  have hsub := rational_sub_encoding B b
  have hmul := rational_mul_encoding ζ b
  have hp := oracleDyadicPrecision_encoding_le_total (B - b) (ζ * b)
  change oracleDyadicPrecision (B - b) (ζ * b) ≤ _
  unfold allocationOracleInputLength
  omega

theorem allocationOracle_eq_boundedPrecision {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    allocationOracle a t σ = allocationOracleWithPrecision a t σ
      (allocationInnerPrecision a t σ) (allocationOuterFuel a t σ) ∧
    allocationInnerPrecision a t σ ≤ 33 * allocationOracleInputLength a t σ + 158 ∧
    allocationOuterFuel a t σ ≤ 30 * allocationOracleInputLength a t σ + 126 := by
  exact ⟨rfl, allocationInnerPrecision_le a t σ, allocationOuterFuel_le a t σ⟩

end IdentityTesting.RationalComputation
