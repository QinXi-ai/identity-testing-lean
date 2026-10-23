import IdentityTesting.CountableRootApproximation
import IdentityTesting.CountableHeadApproximation
import IdentityTesting.PoolingReverseTests
import IdentityTesting.FiniteAllocationUpperZeros

/-! Actual allocation upper tests for arbitrary countable references. All
finite-support/zero-mass and approximation premises are discharged internally. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting
open FiniteAllocationUpper

theorem countable_allocation_upper_bound (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hbranch : largestMass q / 2 ≤ 1 - ε) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (2 * (coarseSampleConstant + 10004)) * allocationRoot q ε := by
  have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < ε :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hε0)
  obtain ⟨m, hm, hsmall, hroot⟩ :=
    (eventually_prefixPooled_head q |>.and
      (hsmall.and (eventually_allocationRoot_prefixPooled_le_twice q hε0 hε1))).exists
  have hres : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
  have hbranchm : largestMass (extendFiniteLaw (prefixPooledFinite q m)) / 2 ≤
      1 - (ε - residualMass q (Finset.range m)) := by
    rw [extendFiniteLaw_prefixPooledFinite, hm.2.2.1]
    linarith
  obtain ⟨n, htest, hn⟩ := finite_allocation_upper_bound_with_zeros
    (prefixPooledFinite q m) (sub_pos.mpr hsmall)
    ((sub_le_self ε hres).trans_lt hε1) hbranchm
  rw [extendFiniteLaw_prefixPooledFinite] at htest hn
  refine ⟨n, hasIdentityTest_countable_of_prefixPooled q m ε n htest, ?_⟩
  have hC : 0 ≤ coarseSampleConstant + 10004 := by norm_num [coarseSampleConstant]
  calc
    (n : ℝ) ≤ (coarseSampleConstant + 10004) *
        allocationRoot (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) := hn
    _ ≤ (coarseSampleConstant + 10004) * (2 * allocationRoot q ε) :=
      mul_le_mul_of_nonneg_left hroot hC
    _ = (2 * (coarseSampleConstant + 10004)) * allocationRoot q ε := by ring

theorem allocation_branch_upper (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hcap : largestMass q ≤ 3 / 4)
    (hbranch : largestMass q / 2 ≤ 1 - ε) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (2 * (coarseSampleConstant + 10004)) * (roundedScale q ε : ℝ) := by
  obtain ⟨n, htest, hn⟩ := countable_allocation_upper_bound q ε hε0 hε1 hbranch
  have hscale : complexityScale q ε = allocationRoot q ε := by
    have hpoint : largestMass q ≠ 1 := ne_of_lt (hcap.trans_lt (by norm_num))
    simp only [complexityScale, ne_of_lt hε1, hpoint, not_lt.mpr hcap,
      hbranch, if_false, if_true]
  have hceil : allocationRoot q ε ≤ (roundedScale q ε : ℝ) := by
    rw [← hscale]
    exact Nat.le_ceil _
  refine ⟨n, htest, hn.trans ?_⟩
  apply mul_le_mul_of_nonneg_left hceil
  norm_num [coarseSampleConstant]

end IdentityTesting
