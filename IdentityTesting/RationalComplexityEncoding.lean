import IdentityTesting.RationalHeavyRootEncoding
import IdentityTesting.RationalMomentEncoding
import IdentityTesting.RationalComplexityScale

/-! Polynomial output representation sizes for the actual complete rational
algorithm. Arithmetic execution cost is a separate statement. -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem rationalMaxValue_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ) :
    L (rationalMaxValue q) ≤ V q := by
  obtain ⟨i, hi⟩ := rationalMaxValue_attained q
  rw [← hi]
  exact rational_entry_encoding_le q i

theorem rationalHeadFirst_encoding (q : Fin (k + 1) → ℚ) : V (rationalHeadFirst q) = V q := by
  unfold rationalVectorEncodingLength
  congr 1
  exact Equiv.sum_comp (rationalHeadSwap q) (fun i => L (q i))

theorem rationalTail_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ) : V (rationalTail q) ≤ V q := by
  rw [← rationalHeadFirst_encoding q]
  unfold rationalVectorEncodingLength
  rw [Fin.sum_univ_succ]
  change k + (∑ i, L (rationalTail q i)) ≤
    k + 1 + (L (rationalHeadFirst q 0) + ∑ i, L (rationalTail q i))
  omega

theorem rationalHeavyInterval_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    L (rationalHeavyInterval q e).1 ≤ 84 * (V q + L e) + 318 ∧
      L (rationalHeavyInterval q e).2 ≤ 84 * (V q + L e) + 318 := by
  cases k with
  | zero => norm_num [rationalHeavyInterval, rationalEncodingLength, numeratorBits, denominatorBits]
  | succ k =>
    obtain ⟨hl, hu⟩ := heavyRootOracle_encoding_le (rationalTail q) e
    have ht := rationalTail_encoding_le q
    dsimp only [rationalHeavyInterval]
    unfold rootInputLength at hl hu
    constructor <;> omega

private theorem encoding_one : L 1 = 3 := by
  norm_num [rationalEncodingLength, numeratorBits, denominatorBits]

theorem rationalExteriorCount_encoding_le (R e : ℚ) :
    L (R / (e - R) ^ 2 + 1 / (e - R)) ≤ 14 * L R + 12 * L e + 13 := by
  have hd := rational_sub_encoding e R
  have hp := rational_pow_encoding (e - R) 2
  have hq := rational_div_encoding_le R ((e - R) ^ 2)
  have hi := rational_reciprocal_encoding (e - R)
  have ha := rational_add_encoding (R / (e - R) ^ 2) (1 / (e - R))
  omega

theorem rationalComplexityInterval_encoding_le {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) :
    let S := V q + L e
    L (rationalComplexityInterval q e).1 ≤ 288 * S ^ 2 + 2536 * S + 5355 ∧
      L (rationalComplexityInterval q e).2 ≤ 288 * S ^ 2 + 2536 * S + 5355 := by
  dsimp only
  let S := V q + L e
  have hV : V q ≤ S := by dsimp [S]; omega
  have he : L e ≤ S := by dsimp [S]; omega
  have hone := encoding_one
  have hmax := rationalMaxValue_encoding_le q
  have hR := rational_sub_encoding 1 (rationalMaxValue q)
  have hδ := rational_sub_encoding 1 e
  unfold rationalComplexityInterval
  dsimp only
  split
  · norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  · split
    · have h := rational_reciprocal_encoding e
      constructor <;> dsimp only <;> omega
    · split
      · split
        · obtain ⟨hl, hu⟩ := rationalHeavyInterval_encoding_le q e
          constructor <;> dsimp only [S] at * <;> omega
        · let R := 1 - rationalMaxValue q
          have hr : L R ≤ 2 * V q + 7 := by dsimp [R]; omega
          obtain ⟨hl, hu⟩ := rationalHeavyInterval_encoding_le q R
          have hb := rationalExteriorCount_encoding_le R e
          have hm1 := rational_min_encoding (rationalHeavyInterval q R).1
            (R / (e - R) ^ 2 + 1 / (e - R))
          have hm2 := rational_min_encoding (rationalHeavyInterval q R).2
            (R / (e - R) ^ 2 + 1 / (e - R))
          change L (min (rationalHeavyInterval q R).1 (R / (e - R) ^ 2 + 1 / (e - R))) ≤ _ ∧
            L (min (rationalHeavyInterval q R).2 (R / (e - R) ^ 2 + 1 / (e - R))) ≤ _
          have hh1 : L (rationalHeavyInterval q R).1 ≤ 252 * S + 906 := by dsimp [S]; omega
          have hh2 : L (rationalHeavyInterval q R).2 ≤ 252 * S + 906 := by dsimp [S]; omega
          have hb' : L (R / (e - R) ^ 2 + 1 / (e - R)) ≤ 40 * S + 111 := by dsimp [S]; omega
          have h1 : L (min (rationalHeavyInterval q R).1 (R / (e - R) ^ 2 + 1 / (e - R))) ≤ 252 * S + 906 := by omega
          have h2 : L (min (rationalHeavyInterval q R).2 (R / (e - R) ^ 2 + 1 / (e - R))) ≤ 252 * S + 906 := by omega
          constructor <;> dsimp only [S] at * <;> omega
      · split
        · obtain ⟨hl, hu⟩ := rationalAllocationRootInterval_encoding_le q e
          constructor <;> unfold rootInputLength at * <;> dsimp only [S] at * <;> omega
        · obtain ⟨hl, hu⟩ := rationalMomentInterval_encoding_le q (1 - e)
          have hT : V q + L (1 - e) ≤ 2 * S + 7 := by dsimp [S]; omega
          have hsq := Nat.mul_le_mul hT hT
          constructor <;> dsimp only [S] at * <;> nlinarith only [hl, hu, hsq, hT]

end IdentityTesting.RationalComputation
