import IdentityTesting.TiltManuscriptBounds
import IdentityTesting.HeavyExteriorTilt

/-! The exact square-root sample bound for the near-exterior deterministic tilt. -/
noncomputable section
namespace IdentityTesting.HeavyExteriorTilt
open FiniteTesting HeavySignedFamily HeavyLowerGeometry DominantTilt EmpiricalSeeds

theorem near_exterior_tilt_sample_bound {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {T Δ c : ℝ} (hT : 0 < T) (hTR : (100000000 : ℝ) ≤ T * tailTotal q)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ tailTotal q / 2)
    (hc0 : 0 ≤ c) (hc : c ≤ 3 / 200) (n : ℕ)
    (hn : (n : ℝ) ≤ c * T) (hnΔ : (n : ℝ) * Δ ^ 2 / tailTotal q ≤ c) :
    ∃ (ν : Probability (Fin (k + 1))) (f : ℝ), 1 ≤ f ∧ f ≤ 2 ∧
      ν.mass 0 = q.mass 0 - (Δ + 4 * Real.sqrt (tailTotal q / T)) ∧
      (∀ i : Fin k, ν.mass i.succ = f * q.mass i.succ) ∧
      FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) ≤
        Real.sqrt ((n : ℝ) * (Δ + 4 * Real.sqrt (tailTotal q / T)) ^ 2 /
          (2 * tailTotal q * (1 - tailTotal q))) ∧
      FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) ≤
        5 * Real.sqrt c / Real.sqrt (2 * (1 - tailTotal q)) := by
  let R := tailTotal q
  let g := Real.sqrt (R / T)
  let d := Δ + 4 * g
  obtain ⟨_, hgR, _⟩ := large_scale_bounds hR0 hT hTR
  change g ≤ R / 10000 at hgR
  have ht := reference_head_tail q
  change q.mass 0 + R = 1 at ht
  have hh : q.mass 0 < 1 := by linarith
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by change R ≤ 1 / 4 at hR; linarith
  have hd0 : 0 ≤ d := by dsimp [d, g]; positivity
  have hdR : d ≤ R := by change Δ ≤ R / 2 at hΔ; dsimp [d]; linarith
  have hdh : d ≤ q.mass 0 := by change R ≤ 1 / 4 at hR; linarith
  have hden : 1 - q.mass 0 = R := by linarith
  have hheadR : q.mass 0 = 1 - R := by linarith
  have hg2 : g ^ 2 = R / T := Real.sq_sqrt (by positivity)
  have hTg : T * g ^ 2 = R := by rw [hg2]; field_simp
  have hnG := mul_le_mul_of_nonneg_right hn (sq_nonneg g)
  rw [mul_assoc, hTg] at hnG
  have hnD : (n : ℝ) * Δ ^ 2 ≤ c * R := (div_le_iff₀ hR0).1 hnΔ
  have hdsq : d ^ 2 ≤ 5 * Δ ^ 2 + 20 * g ^ 2 := by
    dsimp [d]
    nlinarith only [sq_nonneg (Δ - g)]
  have hnsq := mul_le_mul_of_nonneg_left hdsq (Nat.cast_nonneg n)
  have hcost : (n : ℝ) * d ^ 2 ≤ 25 * c * R := by nlinarith only [hnsq, hnG, hnD]
  have hsmall : (n : ℝ) * d ^ 2 / (q.mass 0 * (1 - q.mass 0)) ≤ 1 / 2 := by
    rw [hden]
    apply (div_le_iff₀ (mul_pos (hq 0) hR0)).2
    have hcr := mul_le_mul_of_nonneg_right hc hR0.le
    have hhr := mul_le_mul_of_nonneg_right hhead hR0.le
    change c * R ≤ (3 / 200) * R at hcr
    change (3 / 4) * R ≤ q.mass 0 * R at hhr
    nlinarith only [hcost, hcr, hhr]
  have htv := tiltLaw_productTV_le_sqrt q 0 d hq hh hd0 hdh n hsmall
  have harg : (n : ℝ) * d ^ 2 / (2 * q.mass 0 * (1 - q.mass 0)) ≤
      25 * c / (2 * q.mass 0) := by
    rw [hden]
    apply (div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) (hq 0)) hR0)
      (mul_pos (by norm_num) (hq 0))).2
    have h := mul_le_mul_of_nonneg_right hcost (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (q.nonneg 0))
    nlinarith only [h]
  have heq : Real.sqrt (25 * c / (2 * q.mass 0)) =
      5 * Real.sqrt c / Real.sqrt (2 * (1 - R)) := by
    rw [Real.sqrt_div (by positivity), show (25 : ℝ) * c = 5 ^ 2 * c by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5), hheadR]
  have hf2 : tiltFactor (q.mass 0) d ≤ 2 := by
    unfold tiltFactor
    rw [hden]
    have hquot := (div_le_one hR0).2 hdR
    linarith
  refine ⟨tiltLaw q 0 d hh hd0 hdh, tiltFactor (q.mass 0) d,
    tiltFactor_ge_one hh hd0, hf2, tiltMass_self q 0 d,
    (fun i => tiltMass_ne q 0 d (Fin.succ_ne_zero i)), ?_,
    htv.trans ((Real.sqrt_le_sqrt harg).trans_eq heq)⟩
  have hden' : 2 * q.mass 0 * (1 - q.mass 0) = 2 * R * (1 - R) := by
    rw [hden, hheadR]; ring
  simpa only [hden'] using htv

end IdentityTesting.HeavyExteriorTilt
