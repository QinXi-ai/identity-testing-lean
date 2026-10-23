import IdentityTesting.RationalBisectionEncoding

/-! Encoding lengths of the pole-safe coordinate, budget and objective values
used by the executable allocation oracle. Bounds concern reduced rational
representations, independently of the cost of computing those representations. -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem oracleCoordinateInterval_encoding_le (a β ρ : ℚ) (n : ℕ) :
    rationalEncodingLength (oracleCoordinateInterval a β ρ n).1 ≤
        2 * n + 2 * rationalEncodingLength ρ + 7 ∧
      rationalEncodingLength (oracleCoordinateInterval a β ρ n).2 ≤
        2 * n + 2 * rationalEncodingLength ρ + 7 := by
  obtain ⟨hl, hu⟩ := coordinateInterval_encoding_le a β n
  have hclip := rational_sub_encoding 1 ρ
  have hone : rationalEncodingLength 1 = 3 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  constructor
  · change rationalEncodingLength (coordinateInterval a β n).1 ≤ _
    omega
  · change rationalEncodingLength (min (coordinateInterval a β n).2 (1 - ρ)) ≤ _
    rcases le_total (coordinateInterval a β n).2 (1 - ρ) with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      omega

theorem rationalAllocationCost_encoding_le (t a x : ℚ) :
    rationalEncodingLength (rationalAllocationCost t a x) ≤
      2 * rationalEncodingLength t + 2 * rationalEncodingLength a +
        12 * rationalEncodingLength x + 22 := by
  have ht := rational_pow_encoding t 2
  have ha := rational_pow_encoding a 2
  have hx := rational_pow_encoding x 4
  have hta := rational_mul_encoding (t ^ 2) (a ^ 2)
  have hnum := rational_mul_encoding (t ^ 2 * a ^ 2) (x ^ 4)
  have hden := rational_sub_encoding 1 (x ^ 4)
  have hdiv := rational_div_encoding_le (t ^ 2 * a ^ 2 * x ^ 4) (1 - x ^ 4)
  have hone : rationalEncodingLength 1 = 3 := by
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  unfold rationalAllocationCost
  omega

private theorem sum_encoding_of_pointwise_bound {k : ℕ} (f : Fin k → ℚ)
    (a : Fin k → ℚ) (c b : ℕ)
    (h : ∀ i, rationalEncodingLength (f i) ≤ c * rationalEncodingLength (a i) + b) :
    rationalEncodingLength (∑ i, f i) ≤
      2 * c * rationalVectorEncodingLength a + 2 * k * b + 3 := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have he := rational_sum_encoding Finset.univ f
  have hv : (∑ i, rationalEncodingLength (a i)) ≤ rationalVectorEncodingLength a := by
    unfold rationalVectorEncodingLength
    omega
  have hm := Nat.mul_le_mul_left c hv
  nlinarith

theorem oracleObjectiveInterval_encoding_le {k : ℕ} (a : Fin k → ℚ)
    (β ρ : ℚ) (n : ℕ) :
    rationalEncodingLength (oracleObjectiveInterval a β ρ n).1 ≤
        2 * rationalVectorEncodingLength a +
          2 * k * (2 * n + 2 * rationalEncodingLength ρ + 7) + 3 ∧
      rationalEncodingLength (oracleObjectiveInterval a β ρ n).2 ≤
        2 * rationalVectorEncodingLength a +
          2 * k * (2 * n + 2 * rationalEncodingLength ρ + 7) + 3 := by
  constructor
  · apply sum_encoding_of_pointwise_bound _ a 1
    intro i
    have hm := rational_mul_encoding (a i) (oracleCoordinateInterval (a i) β ρ n).1
    have hx := (oracleCoordinateInterval_encoding_le (a i) β ρ n).1
    omega
  · apply sum_encoding_of_pointwise_bound _ a 1
    intro i
    have hm := rational_mul_encoding (a i) (oracleCoordinateInterval (a i) β ρ n).2
    have hx := (oracleCoordinateInterval_encoding_le (a i) β ρ n).2
    omega

theorem oracleBudgetInterval_encoding_le {k : ℕ} (a : Fin k → ℚ)
    (t β ρ : ℚ) (n : ℕ) :
    rationalEncodingLength (oracleBudgetInterval a t β ρ n).1 ≤
        4 * rationalVectorEncodingLength a +
          2 * k * (2 * rationalEncodingLength t + 24 * n +
            24 * rationalEncodingLength ρ + 106) + 3 ∧
      rationalEncodingLength (oracleBudgetInterval a t β ρ n).2 ≤
        4 * rationalVectorEncodingLength a +
          2 * k * (2 * rationalEncodingLength t + 24 * n +
            24 * rationalEncodingLength ρ + 106) + 3 := by
  constructor
  · apply sum_encoding_of_pointwise_bound _ a 2
    intro i
    have hm := rationalAllocationCost_encoding_le t (a i) (oracleCoordinateInterval (a i) β ρ n).1
    have hx := (oracleCoordinateInterval_encoding_le (a i) β ρ n).1
    omega
  · apply sum_encoding_of_pointwise_bound _ a 2
    intro i
    have hm := rationalAllocationCost_encoding_le t (a i) (oracleCoordinateInterval (a i) β ρ n).2
    have hx := (oracleCoordinateInterval_encoding_le (a i) β ρ n).2
    omega

end IdentityTesting.RationalComputation
