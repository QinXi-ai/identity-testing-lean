import IdentityTesting.FiniteOverlapMoment

/-! Explicit sample rounding and scalar bounds for the moment tester. -/
noncomputable section
namespace IdentityTesting.MomentTesting

theorem ceil_ratio_bounds {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1) :
    a ≤ (⌈a / b⌉₊ : ℝ) * b ∧ (⌈a / b⌉₊ : ℝ) * b ≤ a + 1 := by
  constructor
  · exact (div_le_iff₀ hb).mp (Nat.le_ceil (a / b))
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ a / b by positivity)
    have h := mul_le_mul_of_nonneg_right hc.le hb.le
    rw [add_mul, div_mul_cancel₀ _ hb.ne', one_mul] at h
    linarith

theorem moment_sample_bounds {δ W A B : ℝ} (hδ : 0 < δ) (hW : 0 < W) (hW1 : W ≤ 1)
    (hregime : 1000000000000 * δ < W)
    (hA : Real.sqrt δ * W / 2 ≤ A) (hB : 0 ≤ B) (hBW : B ≤ δ * W) :
    let n := ⌈10000 / W⌉₊
    2 ≤ n ∧ (n : ℝ) ≤ 10001 / W ∧
      200 * Real.sqrt δ ≤ (n : ℝ) * A ∧
      (n : ℝ) ^ 2 * B ≤ 1 / 100 ∧
      4 * Real.sqrt δ * δ ≤ A ∧
      16000000 * δ ≤ (n : ℝ) ^ 2 * A ^ 2 := by
  dsimp only
  let N : ℝ := ⌈10000 / W⌉₊
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  obtain ⟨hNW0, hNW1⟩ := ceil_ratio_bounds (a := 10000) (by norm_num) hW hW1
  change 10000 ≤ N * W at hNW0
  norm_num only [show (10000 : ℝ) + 1 = 10001 by norm_num] at hNW1
  change N * W ≤ 10001 at hNW1
  have hNlarge : 10000 ≤ N := by
    have h := mul_le_mul_of_nonneg_left hW1 hN0
    linarith
  have hn : 2 ≤ ⌈10000 / W⌉₊ := by
    have h : (2 : ℝ) ≤ (⌈10000 / W⌉₊ : ℝ) := by change 2 ≤ N; linarith
    exact_mod_cast h
  have hNbound : N ≤ 10001 / W := (le_div_iff₀ hW).mpr hNW1
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hNA : 5000 * Real.sqrt δ ≤ N * A := by
    have h1 := mul_le_mul_of_nonneg_left hA hN0
    have h2 := mul_le_mul_of_nonneg_left hNW0 hs.le
    nlinarith only [h1, h2]
  have hcollision : N ^ 2 * B ≤ 1 / 100 := by
    have h3 : (N * W) ^ 2 ≤ 10001 ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hN0 hW.le) hNW1 2
    have hBW' : B / W ^ 2 ≤ (1 : ℝ) / 1000000000000 := by
      apply (div_le_iff₀ (sq_pos_of_pos hW)).mpr
      have h := mul_le_mul_of_nonneg_right hregime.le hW.le
      nlinarith only [h, hBW]
    have hb : N ^ 2 * B = (N * W) ^ 2 * (B / W ^ 2) := by
      field_simp
    rw [hb]
    have hp := mul_le_mul h3 hBW' (div_nonneg hB (sq_nonneg W)) (by norm_num : (0 : ℝ) ≤ 10001 ^ 2)
    exact hp.trans (by norm_num)
  have hsmall : 4 * Real.sqrt δ * δ ≤ A := by
    have h := mul_le_mul_of_nonneg_left hregime.le hs.le
    have hd := mul_nonneg hs.le hδ.le
    nlinarith only [h, hA, hd]
  have hsignal : 16000000 * δ ≤ N ^ 2 * A ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 5000 * Real.sqrt δ) hNA 2
    nlinarith only [hsq, Real.sq_sqrt hδ.le, hδ]
  exact ⟨hn, hNbound, by linarith [Real.sqrt_nonneg δ], hcollision, hsmall, hsignal⟩

end IdentityTesting.MomentTesting
