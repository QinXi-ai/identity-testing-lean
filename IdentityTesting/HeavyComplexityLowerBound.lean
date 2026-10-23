import IdentityTesting.HeavyRootLowerBound
import IdentityTesting.HeavyExteriorRootLowerBound

/-! # The original complexityScale lower obstruction for finite heavy laws -/

noncomputable section
namespace IdentityTesting

open FiniteTesting HeavySignedFamily

theorem no_identityTest_of_finite_heavy_complexityScale {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q < (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 11) * complexityScale (extendFiniteLaw q) ε) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  have hmass := largestMass_extendFiniteLaw_heavy q hR.le
  have htotal := reference_head_tail q
  have hRformula : 1 - q.mass 0 = tailTotal q := by linarith only [htotal]
  have hheadne : q.mass 0 ≠ 1 := by linarith only [htotal, hR0]
  have hheadgt : (3 : ℝ) / 4 < q.mass 0 := by linarith only [htotal, hR]
  have hscale : complexityScale (extendFiniteLaw q) ε =
      if ε ≤ tailTotal q then heavyRoot (extendFiniteLaw q) ε else
        min (heavyRoot (extendFiniteLaw q) (tailTotal q))
          (tailTotal q / (ε - tailTotal q) ^ 2 + 1 / (ε - tailTotal q)) := by
    simp only [complexityScale, hmass, ne_of_lt hε1, hheadne, hheadgt, if_false, if_true, hRformula]
  rw [hscale] at hn
  by_cases hεR : ε ≤ tailTotal q
  · rw [if_pos hεR] at hn
    have hT := heavyRoot_pos (extendFiniteLaw q) (by rw [hmass]; linarith only [htotal, hR0]) hε0
    apply no_identityTest_of_finite_heavyRoot q hq hR0 hR.le hε0 hεR n
    exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) hT.le)
  · rw [if_neg hεR] at hn
    have hΔ : 0 < ε - tailTotal q := sub_pos.mpr (lt_of_not_ge hεR)
    have hsum : tailTotal q + (ε - tailTotal q) = ε := by ring
    have h := no_identityTest_of_finite_heavy_exterior q hq hR0 hR.le hΔ
      (by rwa [hsum]) n hn
    rwa [hsum] at h

theorem finite_heavy_roundedScale_lower {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q < (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (htest : HasIdentityTest (extendFiniteLaw q) ε n) :
    (1 / (10 : ℝ) ^ 11) * (roundedScale (extendFiniteLaw q) ε : ℝ) ≤ n := by
  have hscale : (1 / (10 : ℝ) ^ 11) * complexityScale (extendFiniteLaw q) ε < (n : ℝ) := by
    apply lt_of_not_ge
    intro hn
    exact no_identityTest_of_finite_heavy_complexityScale q hq hR0 hR hε0 hε1 n hn htest
  have hceil : roundedScale (extendFiniteLaw q) ε ≤ 100000000000 * n := by
    apply Nat.ceil_le.mpr
    push_cast
    norm_num at hscale ⊢
    linarith only [hscale]
  have hreal : (roundedScale (extendFiniteLaw q) ε : ℝ) ≤ 100000000000 * (n : ℝ) := by
    exact_mod_cast hceil
  norm_num
  linarith only [hreal]

end IdentityTesting
