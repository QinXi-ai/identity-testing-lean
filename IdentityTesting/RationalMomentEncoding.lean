import IdentityTesting.RationalSqrtEncoding
import IdentityTesting.RationalMomentInterval

/-! Original-input bounds for the rational moment interval. -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem rationalMomentUpper_encoding_le {k : ℕ} (q : Fin k → ℚ) (δ : ℚ) :
    L (rationalMomentUpper q δ) ≤
      74 * V q + 2 * k * (36 * L δ + 93) + 3 := by
  have hterm (i : Fin k) : L (min (q i) (q i * dyadicSqrtUpper (q i / δ))) ≤
      37 * L (q i) + 36 * L δ + 93 := by
    have hd := rational_div_encoding_le (q i) δ
    have hs := dyadicSqrtUpper_encoding_le (q i / δ)
    have hm := rational_mul_encoding (q i) (dyadicSqrtUpper (q i / δ))
    have hmin := rational_min_encoding (q i) (q i * dyadicSqrtUpper (q i / δ))
    omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have h := rational_sum_encoding Finset.univ
    (fun i => min (q i) (q i * dyadicSqrtUpper (q i / δ)))
  unfold rationalMomentUpper rationalVectorEncodingLength
  nlinarith

theorem rationalMomentInterval_encoding_le {k : ℕ} (q : Fin k → ℚ) (δ : ℚ) :
    let S := V q + L δ
    L (rationalMomentInterval q δ).1 ≤ 72 * S ^ 2 + 260 * S + 7 ∧
      L (rationalMomentInterval q δ).2 ≤ 72 * S ^ 2 + 260 * S + 7 := by
  dsimp only
  let S := V q + L δ
  have h := rationalMomentUpper_encoding_le q δ
  have hk : k ≤ S := by dsimp [S, rationalVectorEncodingLength]; omega
  have hV : V q ≤ S := by dsimp [S]; omega
  have hδ : L δ ≤ S := by dsimp [S]; omega
  have hmul := Nat.mul_le_mul hk hδ
  have h1 := rational_reciprocal_encoding (rationalMomentUpper q δ)
  have h2 := rational_div_encoding_le 2 (rationalMomentUpper q δ)
  have htwo : L 2 = 4 := by
    have h : (2 : ℕ).size = 2 := by simpa using (Nat.size_pow (n := 1))
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]
  dsimp only [rationalMomentInterval]
  constructor <;> dsimp only [S] at * <;> nlinarith

end IdentityTesting.RationalComputation
