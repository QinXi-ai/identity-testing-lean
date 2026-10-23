import IdentityTesting.HeavyUncompressedPrior
import IdentityTesting.FinitePriorProduct

/-! A test whose alternatives range only over the finite reference support.
For a positive q on Fin k this is exactly the manuscript's stronger restricted
alternative model, with the same strict TV separation and both errors <=1/3. -/

noncomputable section
namespace IdentityTesting.HeavyRestrictedSupport
open scoped BigOperators
open Classical FiniteTesting HeavySignedFamily HeavyTilt DominantTilt EmpiricalSeeds

def HasFiniteSupportTest {k : ℕ} (q : Probability (Fin k)) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ test : FiniteTesting.RandomizedTest (Fin n → Fin k),
    expectation (productLaw q n) test ≤ (1 : ℝ) / 3 ∧
      ∀ p : Probability (Fin k), ε < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ (1 : ℝ) / 3

theorem no_supportTest_of_finite_prior {k : ℕ} {I : Type*} [Fintype I]
    (weights : Probability I) (family : I → Probability (Fin k))
    (q : Probability (Fin k)) (ε : ℝ) (n : ℕ)
    (hsep : ∀ i, 0 < weights.mass i → ε < FiniteTesting.totalVariation (family i) q)
    (hTV : FiniteTesting.totalVariation (mixture weights (fun i => productLaw (family i) n))
      (productLaw q n) < (1 : ℝ) / 3) : ¬ HasFiniteSupportTest q ε n := by
  rintro ⟨test, hnull, halt⟩
  apply finite_iid_prior_obstruction_on_support weights family q ε n hsep hTV
  exact ⟨test, hnull, fun p hp => by linarith only [halt p hp]⟩

/-- The existing small-scale tilt, terminated in the finite-support testing
model. The actual law and its chi-square formula are reused unchanged. -/
theorem no_supportTest_small_scale_lt_two {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {T ε : ℝ}
    (hTR : T * tailTotal q < (100000000 : ℝ)) (hε : ε < 2 * tailTotal q)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ¬ HasFiniteSupportTest q ε n := by
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
  apply no_supportTest_of_finite_prior (SignedDiagonalMoment.uniformSigns k) (fun _ => ν) q ε n
  · intro σ _
    rw [hνTV]
    exact hε
  · simpa only [mixture_constant] using hsmall

theorem no_supportTest_zero {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {ε : ℝ}
    (hε : ε < 2 * tailTotal q) : ¬ HasFiniteSupportTest q ε 0 :=
  no_supportTest_small_scale_lt_two q hq hR0 hR (T := 1) (by linarith) hε 0 (by norm_num)

end IdentityTesting.HeavyRestrictedSupport
