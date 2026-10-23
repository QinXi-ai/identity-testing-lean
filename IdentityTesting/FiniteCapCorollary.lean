import IdentityTesting.MinimumSampleComplexity
import IdentityTesting.FiniteTestingRelabeling
import IdentityTesting.FiniteAllocationUpperZeros
import IdentityTesting.MomentFiniteTransfer
import IdentityTesting.MomentLowerBound

/-! Original `gen:complete` at cap 4/5, in terms of the literal minimum
natural sample size and the unrounded allocation/moment quantities. -/

noncomputable section
namespace IdentityTesting
open FiniteTesting

theorem finite_minimum_allocation_bounds {k : ℕ} (q : Probability (Fin k))
    (hcap : largestMass (extendFiniteLaw q) ≤ (4 : ℝ) / 5)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    (1 / (10 : ℝ) ^ 12) * allocationRoot (extendFiniteLaw q) ε ≤
        (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ∧
      (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤
        (FiniteAllocationUpper.coarseSampleConstant + 10004) * allocationRoot (extendFiniteLaw q) ε := by
  have hm := minimumSampleComplexity_isLeast (extendFiniteLaw q) hε0 hε1.le
  have hcap' : ∀ i, q.mass i ≤ (4 : ℝ) / 5 := by
    intro i
    have hi := largestIndex_spec (extendFiniteLaw q) i.val
    rw [← largestMass_eq_selected, extendFiniteLaw_mass_val] at hi
    exact hi.trans hcap
  refine ⟨le_of_lt (lt_of_not_ge (fun hn =>
    no_identityTest_of_general_allocation_root_with_zeros q hcap' ε hε0 hε1 _ hn hm.1)), ?_⟩
  obtain ⟨n, ht, hn⟩ := FiniteAllocationUpper.finite_allocation_upper_bound_with_zeros q hε0 hε1 hbranch
  exact (show (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤ (n : ℝ) by
    exact_mod_cast hm.2 ht).trans hn

theorem finite_minimum_moment_bounds {k : ℕ} (q : Probability (Fin k))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hbranch : 1 - ε ≤ largestMass (extendFiniteLaw q) / 2) :
    (1 : ℝ) / 1000 / overlapMoment (extendFiniteLaw q) (1 - ε) ≤
        (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ∧
      (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤
        50000000000001 / overlapMoment (extendFiniteLaw q) (1 - ε) := by
  have hδ : 0 < 1 - ε := sub_pos.mpr hε1
  have hm := minimumSampleComplexity_isLeast (extendFiniteLaw q) hε0 hε1.le
  refine ⟨le_of_lt (lt_of_not_ge (fun hn =>
    no_identityTest_of_overlap_moment q (1 - ε) hδ _ hn
      (by simpa only [sub_sub_cancel] using hm.1))), ?_⟩
  have hs : ∀ i, i ∉ Finset.range k → (extendFiniteLaw q).mass i = 0 := by
    intro i hi
    exact extendFiniteLaw_mass_of_not_lt q i (fun hit => hi (Finset.mem_range.mpr hit))
  obtain ⟨n, ht, hn⟩ := MomentTesting.hasIdentityTest_moment_of_finite_support_sharp
    (extendFiniteLaw q) (Finset.range k) hs (1 - ε) hδ (by linarith)
  have ht' : HasIdentityTest (extendFiniteLaw q) ε n := by simpa only [sub_sub_cancel] using ht
  exact (show (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤ (n : ℝ) by
    exact_mod_cast hm.2 ht').trans hn

/-- `gen:complete`, with one pair of universal constants for both closed
branches. There is no extra max(1,.) or rounded scale in the result. -/
theorem finite_cap_four_fifths_all_radius {k : ℕ} (q : Probability (Fin k))
    (hcap : largestMass (extendFiniteLaw q) ≤ (4 : ℝ) / 5)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε →
      (1 / (10 : ℝ) ^ 12) * allocationRoot (extendFiniteLaw q) ε ≤
          (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ∧
        (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤
          (10 : ℝ) ^ 42 * allocationRoot (extendFiniteLaw q) ε) ∧
    (1 - ε ≤ largestMass (extendFiniteLaw q) / 2 →
      (1 / (10 : ℝ) ^ 12) * (1 / overlapMoment (extendFiniteLaw q) (1 - ε)) ≤
          (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ∧
        (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤
          (10 : ℝ) ^ 42 * (1 / overlapMoment (extendFiniteLaw q) (1 - ε))) := by
  constructor
  · intro hb
    obtain ⟨hl, hu⟩ := finite_minimum_allocation_bounds q hcap hε0 hε1 hb
    refine ⟨hl, hu.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by norm_num [FiniteAllocationUpper.coarseSampleConstant])
      (allocationRoot_spec (extendFiniteLaw q) hε0 hε1).1.le
  · intro hb
    obtain ⟨hl, hu⟩ := finite_minimum_moment_bounds q hε0 hε1 hb
    have hW := overlapMoment_pos (extendFiniteLaw q) (sub_pos.mpr hε1)
    constructor
    · apply le_trans _ hl
      convert div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) / 10 ^ 12 ≤ 1 / 1000) hW.le using 1 <;> ring
    · apply hu.trans
      convert div_le_div_of_nonneg_right (by norm_num : (50000000000001 : ℝ) ≤ 10 ^ 42) hW.le using 1 <;> ring

/-- Both original formulas apply at δ=h/2, hence they are universally
comparable; this uses the actual common minimum sample count. -/
theorem finite_branch_boundary_comparison {k : ℕ} (q : Probability (Fin k))
    (hcap : largestMass (extendFiniteLaw q) ≤ (4 : ℝ) / 5)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hboundary : 1 - ε = largestMass (extendFiniteLaw q) / 2) :
    allocationRoot (extendFiniteLaw q) ε ≤
        (10 : ℝ) ^ 54 * (1 / overlapMoment (extendFiniteLaw q) (1 - ε)) ∧
      (1 / overlapMoment (extendFiniteLaw q) (1 - ε)) ≤
        (10 : ℝ) ^ 54 * allocationRoot (extendFiniteLaw q) ε := by
  obtain ⟨ha, hm⟩ := finite_cap_four_fifths_all_radius q hcap hε0 hε1
  obtain ⟨hal, hau⟩ := ha hboundary.ge
  obtain ⟨hml, hmu⟩ := hm hboundary.le
  constructor <;> norm_num at * <;> linarith

end IdentityTesting
