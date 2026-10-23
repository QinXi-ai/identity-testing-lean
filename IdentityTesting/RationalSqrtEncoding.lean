import IdentityTesting.RationalRootSearchEncoding
import IdentityTesting.RationalSqrtInterval

/-! Representation bounds for the actual rational square-root bisection. -/

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem sqrtInitialUpper_encoding_le (a : ℚ) : L (sqrtInitialUpper a) ≤ 4 * L a + 7 := by
  have hc : Nat.ceil a ≤ 2 ^ numeratorBits a := Nat.ceil_le.mpr
    (by exact_mod_cast (rational_lt_pow_numeratorBits a).le)
  have hs := Nat.size_le_size hc
  rw [Nat.size_pow] at hs
  have hn : numeratorBits a ≤ L a := by unfold rationalEncodingLength; omega
  have h2 : L 2 = 4 := by
    have h : (2 : ℕ).size = 2 := by simpa using (Nat.size_pow (n := 1))
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h]
  have hp := rational_pow_encoding 2 (Nat.ceil a).size
  rw [h2] at hp
  unfold sqrtInitialUpper
  omega

theorem sqrtInterval_precision_encoding_le (a δ : ℚ) :
    oracleDyadicPrecision (sqrtInitialUpper a) δ ≤ 4 * L a + L δ + 8 := by
  have h := oracleDyadicPrecision_encoding_le_total (sqrtInitialUpper a) δ
  have hU := sqrtInitialUpper_encoding_le a
  omega

private theorem bisect_output_grid_encoding (p : ℚ → ℚ) (b B : ℚ)
    (fuel s j : ℕ) (hj : j < 2 ^ s) :
    let I := bisect p fuel (dyadicAffine b B s j) (dyadicAffine b B s (j + 1))
    let K := 6 * L b + 4 * L B + 4 * (s + fuel) + 9
    L I.1 ≤ K ∧ L I.2 ≤ K := by
  dsimp only
  induction fuel generalizing s j with
  | zero =>
    have hl := dyadicAffine_encoding_le b B s j hj.le
    have hu := dyadicAffine_encoding_le b B s (j + 1) (by omega)
    simp only [bisect]
    constructor <;> omega
  | succ fuel ih =>
    obtain ⟨hl, hu, hm⟩ := dyadicAffine_step b B s j
    have hjl : 2 * j < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hjr : 2 * j + 1 < 2 ^ (s + 1) := by rw [pow_succ]; omega
    simp only [bisect, hm]
    split
    · rw [hu]
      obtain ⟨h1, h2⟩ := ih (s + 1) (2 * j + 1) hjr
      constructor <;> omega
    · rw [hl]
      obtain ⟨h1, h2⟩ := ih (s + 1) (2 * j) hjl
      constructor <;> omega

theorem bisect_output_encoding_le (p : ℚ → ℚ) (fuel : ℕ) (b B : ℚ) :
    L (bisect p fuel b B).1 ≤ 6 * L b + 4 * L B + 4 * fuel + 9 ∧
      L (bisect p fuel b B).2 ≤ 6 * L b + 4 * L B + 4 * fuel + 9 := by
  simpa [dyadicAffine] using bisect_output_grid_encoding p b B fuel 0 0 (by norm_num)

theorem sqrtInterval_encoding_le (a δ : ℚ) :
    L (sqrtInterval a δ).1 ≤ 32 * L a + 4 * L δ + 81 ∧
      L (sqrtInterval a δ).2 ≤ 32 * L a + 4 * L δ + 81 := by
  have hf := sqrtInterval_precision_encoding_le a δ
  have hU := sqrtInitialUpper_encoding_le a
  have hzero : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  obtain ⟨hl, hu⟩ := bisect_output_encoding_le (fun x => x ^ 2 - a)
    (oracleDyadicPrecision (sqrtInitialUpper a) δ) 0 (sqrtInitialUpper a)
  unfold sqrtInterval
  constructor <;> omega

theorem dyadicSqrtUpper_encoding_le (a : ℚ) : L (dyadicSqrtUpper a) ≤ 36 * L a + 93 := by
  have h := (sqrtInterval_encoding_le a (min 1 a)).2
  have hm := rational_min_encoding 1 a
  have hone : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  unfold dyadicSqrtUpper
  omega

end IdentityTesting.RationalComputation
