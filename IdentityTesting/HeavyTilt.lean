import IdentityTesting.HeavyLowerGeometry
import IdentityTesting.FiniteCoupling

/-! # Actual heavy-head deterministic tilts, at small and large count scales -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavyTilt

open FiniteTesting HeavySignedFamily HeavyLowerGeometry DominantTilt EmpiricalSeeds

variable {k : ℕ}

theorem sample_tv_lt_of_rate (p q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    {T : ℝ} (hT : 0 < T) (hrate : FiniteChiSquare.chiSquare p q ≤ 80 / T)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    FiniteTesting.totalVariation (productLaw p n) (productLaw q n) < 1 / (10 : ℝ) ^ 4 := by
  have hexponent : (n : ℝ) * FiniteChiSquare.chiSquare p q ≤ 80 / (10 : ℝ) ^ 10 := by
    calc
      _ ≤ (n : ℝ) * (80 / T) := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg n)
      _ = 80 * (n : ℝ) / T := by ring
      _ ≤ _ := by
        apply (div_le_iff₀ hT).2
        have h := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 80)
        convert h using 1; ring
  have hexp := (Real.exp_le_exp.mpr hexponent).trans (Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 80 / (10 : ℝ) ^ 10) (by norm_num))
  have hchi := chiSquare_productLaw_le_exp p q n
  have hnum : (1 : ℝ) / (1 - 80 / (10 : ℝ) ^ 10) - 1 < 4 / (10 : ℝ) ^ 8 := by norm_num
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four (productLaw p n) (productLaw q n)
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  by_contra hnot
  have hlarge : 1 / (10 : ℝ) ^ 4 ≤ FiniteTesting.totalVariation (productLaw p n) (productLaw q n) := le_of_not_gt hnot
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 4) hlarge
  norm_num at hsq
  nlinarith only [hexp, hchi, hnum, hTV, hsq]

theorem exists_large_heavy_tilt (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {T : ℝ} (hT : 0 < T)
    (hTR : (100000000 : ℝ) ≤ T * tailTotal q) :
    ∃ (ν : Probability (Fin (k + 1))) (f : ℝ), 1 ≤ f ∧ f ≤ 2 ∧
      (∀ j, 0 < ν.mass j) ∧
      ν.mass 0 = q.mass 0 - 4 * Real.sqrt (tailTotal q / T) ∧
      (∀ i : Fin k, ν.mass i.succ = f * q.mass i.succ) ∧
      (∀ s : Finset (Fin (k + 1)), 0 ∈ s →
        (∑ j ∈ s, min (ν.mass j) (q.mass j)) =
          (∑ j ∈ s, q.mass j) - 4 * Real.sqrt (tailTotal q / T)) ∧
      FiniteChiSquare.chiSquare ν q ≤ 80 / T ∧
      (∀ n : ℕ, (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T →
        FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) < 1 / (10 : ℝ) ^ 4) := by
  let R := tailTotal q
  let g := Real.sqrt (R / T)
  obtain ⟨hg, hgR, hTg⟩ := large_scale_bounds hR0 hT hTR
  have htotal := reference_head_tail q
  have hh : q.mass 0 < 1 := by linarith only [htotal, hR0]
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by linarith only [htotal, hR]
  have hσ0 : 0 ≤ 4 * g := by dsimp [g, R]; positivity
  have hσlt : 4 * g < q.mass 0 := by
    change g ≤ R / 10000 at hgR
    change R ≤ 1 / 4 at hR
    nlinarith only [hgR, hR, hhead]
  let ν := tiltLaw q 0 (4 * g) hh hσ0 hσlt.le
  have hχ : FiniteChiSquare.chiSquare ν q ≤ 80 / T := by
    rw [tiltLaw_chiSquare q 0 (4 * g) hh hσ0 hσlt.le hq]
    have hden : 1 - q.mass 0 = R := by change q.mass 0 + R = 1 at htotal; linarith only [htotal]
    rw [hden]
    apply (div_le_div_iff₀ (mul_pos (hq 0) hR0) hT).2
    have hg2 : g ^ 2 = R / T := Real.sq_sqrt (div_nonneg hR0.le hT.le)
    have hTg2 : T * g ^ 2 = R := by rw [hg2]; field_simp
    have hprod := mul_nonneg hR0.le (sub_nonneg.mpr hhead)
    change q.mass 0 + R = 1 at htotal
    nlinarith only [hTg2, hprod, hR0]
  have hf2 : tiltFactor (q.mass 0) (4 * g) ≤ 2 := by
    unfold tiltFactor
    have heq : 1 - q.mass 0 = R := by change q.mass 0 + R = 1 at htotal; linarith only [htotal]
    rw [heq]
    have hquot : (4 * g) / R ≤ 1 := (div_le_iff₀ hR0).2 (by
      change g ≤ R / 10000 at hgR
      linarith only [hgR, hR0])
    linarith only [hquot]
  refine ⟨ν, tiltFactor (q.mass 0) (4 * g), tiltFactor_ge_one hh hσ0, hf2,
    tiltLaw_positive q 0 (4 * g) hh hσ0 hσlt.le hq hσlt, ?_, ?_, ?_, hχ, ?_⟩
  · exact tiltMass_self q 0 (4 * g)
  · intro i
    exact tiltMass_ne q 0 (4 * g) (Fin.succ_ne_zero i)
  · intro s hs
    exact tiltLaw_overlap q 0 (4 * g) hh hσ0 hσlt.le s hs
  · intro n hn
    exact sample_tv_lt_of_rate ν q hq hT hχ n hn

theorem no_identityTest_of_small_heavy_scale_lt_two
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {T ε : ℝ}
    (hTR : T * tailTotal q < (100000000 : ℝ)) (hε : ε < 2 * tailTotal q)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  let R := tailTotal q
  have htotal := reference_head_tail q
  have hh : q.mass 0 < 1 := by linarith only [htotal, hR0]
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by linarith only [htotal, hR]
  have hσ0 : 0 ≤ 2 * R := mul_nonneg (by norm_num) hR0.le
  have hσh : 2 * R ≤ q.mass 0 := by
    change R ≤ 1 / 4 at hR
    linarith only [hhead, hR]
  let ν := tiltLaw q 0 (2 * R) hh hσ0 hσh
  have hνTV : FiniteTesting.totalVariation ν q = 2 * R := by
    have h := tiltLaw_overlap q 0 (2 * R) hh hσ0 hσh Finset.univ (Finset.mem_univ 0)
    rw [q.total] at h
    rw [finite_totalVariation_eq_one_sub_overlap]
    linarith only [h]
  have hchi : FiniteChiSquare.chiSquare ν q ≤ 8 * R := by
    rw [tiltLaw_chiSquare q 0 (2 * R) hh hσ0 hσh hq]
    have heq : 1 - q.mass 0 = R := by change q.mass 0 + R = 1 at htotal; linarith only [htotal]
    rw [heq]
    have hformula : (2 * R) ^ 2 / (q.mass 0 * R) = 4 * R / q.mass 0 := by
      field_simp [ne_of_gt hR0, ne_of_gt (hq 0)]
      ring
    rw [hformula]
    apply (div_le_iff₀ (hq 0)).2
    have h := mul_le_mul_of_nonneg_left hhead (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hR0.le)
    nlinarith only [h, hR0]
  have hnR : (n : ℝ) * R < 1 / 100 := by
    have h := mul_le_mul_of_nonneg_right hn hR0.le
    change T * R < 100000000 at hTR
    norm_num at h
    nlinarith only [h, hTR]
  have hexponent : (n : ℝ) * FiniteChiSquare.chiSquare ν q ≤ 1 / 10 := by
    have h := mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)
    nlinarith only [h, hnR]
  have hexp := (Real.exp_le_exp.mpr hexponent).trans (Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num))
  have hchinp := chiSquare_productLaw_le_exp ν q n
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four (productLaw ν n) (productLaw q n)
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  have hsmall : FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) < (1 : ℝ) / 3 := by
    by_contra hnot
    have hlarge : (1 : ℝ) / 3 ≤ FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) := le_of_not_gt hnot
    have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 3) hlarge
    norm_num at hexp hsq
    nlinarith only [hexp, hchinp, hTV, hsq]
  apply no_identityTest_extendFiniteLaw_of_finite_prior (SignedDiagonalMoment.uniformSigns k) (fun _ => ν) q ε n
  · intro σ _
    rw [hνTV]
    exact hε
  · simpa only [mixture_constant] using hsmall

theorem no_identityTest_of_small_heavy_scale
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {T ε : ℝ}
    (hTR : T * tailTotal q < (100000000 : ℝ)) (hε : ε ≤ tailTotal q)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  exact no_identityTest_of_small_heavy_scale_lt_two q hq hR0 hR hTR
    (by linarith only [hε, hR0]) n hn

end IdentityTesting.HeavyTilt
