import IdentityTesting.TiltManuscriptBounds
import IdentityTesting.HeavyTilt

/-! Exact square-root sample bounds for the manuscript's heavy-head tilts. -/
noncomputable section
namespace IdentityTesting.HeavyTilt
open FiniteTesting HeavySignedFamily HeavyLowerGeometry DominantTilt EmpiricalSeeds

theorem large_heavy_tilt_sample_bound {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {T c : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c) (hc : c ≤ 3 / 128)
    (hTR : (100000000 : ℝ) ≤ T * tailTotal q) (n : ℕ)
    (hn : (n : ℝ) ≤ c * T) :
    ∃ (ν : Probability (Fin (k + 1))) (f : ℝ), 1 ≤ f ∧ f ≤ 2 ∧
      (∀ j, 0 < ν.mass j) ∧
      ν.mass 0 = q.mass 0 - 4 * Real.sqrt (tailTotal q / T) ∧
      (∀ i : Fin k, ν.mass i.succ = f * q.mass i.succ) ∧
      FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) ≤
        Real.sqrt ((n : ℝ) * (4 * Real.sqrt (tailTotal q / T)) ^ 2 /
          (2 * tailTotal q * (1 - tailTotal q))) ∧
      FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) ≤
        4 * Real.sqrt (2 * c / 3) := by
  let R := tailTotal q
  let g := Real.sqrt (R / T)
  have ht := reference_head_tail q
  change q.mass 0 + R = 1 at ht
  have hh : q.mass 0 < 1 := by linarith
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by change R ≤ 1 / 4 at hR; linarith
  obtain ⟨hg, hgR, _⟩ := large_scale_bounds hR0 hT hTR
  change g ≤ R / 10000 at hgR
  have hσ0 : 0 ≤ 4 * g := by dsimp [g]; positivity
  have hσlt : 4 * g < q.mass 0 := by change R ≤ 1 / 4 at hR; nlinarith
  let ν := tiltLaw q 0 (4 * g) hh hσ0 hσlt.le
  have hden : 1 - q.mass 0 = R := by linarith
  have hg2 : g ^ 2 = R / T := Real.sq_sqrt (by positivity)
  have hTg : T * g ^ 2 = R := by rw [hg2]; field_simp
  have hbound : (n : ℝ) * (4 * g) ^ 2 / (q.mass 0 * (1 - q.mass 0)) ≤ 64 * c / 3 := by
    rw [hden]
    apply (div_le_iff₀ (mul_pos (hq 0) hR0)).2
    have hng := mul_le_mul_of_nonneg_right hn (sq_nonneg g)
    rw [mul_assoc, hTg] at hng
    have hheadc := mul_le_mul_of_nonneg_left hhead (mul_nonneg hc0 hR0.le)
    change c * R * (3 / 4) ≤ c * R * q.mass 0 at hheadc
    nlinarith only [hng, hheadc]
  have htv := tiltLaw_productTV_le_sqrt q 0 (4 * g) hq hh hσ0 hσlt.le n
    (hbound.trans (by linarith))
  have hsqrt : Real.sqrt ((n : ℝ) * (4 * g) ^ 2 /
      (2 * q.mass 0 * (1 - q.mass 0))) ≤ 4 * Real.sqrt (2 * c / 3) := by
    have hs := Real.sqrt_le_sqrt (show (n : ℝ) * (4 * g) ^ 2 /
        (2 * q.mass 0 * (1 - q.mass 0)) ≤ 32 * c / 3 by
      have heq : (n : ℝ) * (4 * g) ^ 2 / (2 * q.mass 0 * (1 - q.mass 0)) =
          ((n : ℝ) * (4 * g) ^ 2 / (q.mass 0 * (1 - q.mass 0))) / 2 := by
        rw [show 2 * q.mass 0 * (1 - q.mass 0) = (q.mass 0 * (1 - q.mass 0)) * 2 by ring,
          div_mul_eq_div_div]
      rw [heq]; linarith)
    have heq : Real.sqrt (32 * c / 3) = 4 * Real.sqrt (2 * c / 3) := by
      rw [show 32 * c / 3 = (4 : ℝ) ^ 2 * (2 * c / 3) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    exact hs.trans_eq heq
  have hf2 : tiltFactor (q.mass 0) (4 * g) ≤ 2 := by
    unfold tiltFactor
    rw [hden]
    have hquot : 4 * g / R ≤ 1 := (div_le_iff₀ hR0).2 (by linarith)
    linarith
  refine ⟨ν, tiltFactor (q.mass 0) (4 * g), tiltFactor_ge_one hh hσ0, hf2,
    tiltLaw_positive q 0 (4 * g) hh hσ0 hσlt.le hq hσlt,
    tiltMass_self q 0 (4 * g), (fun i => tiltMass_ne q 0 (4 * g) (Fin.succ_ne_zero i)),
    ?_, htv.trans hsqrt⟩
  have heq : 2 * q.mass 0 * (1 - q.mass 0) = 2 * R * (1 - R) := by rw [hden]; nlinarith
  simpa only [heq] using htv

end IdentityTesting.HeavyTilt
