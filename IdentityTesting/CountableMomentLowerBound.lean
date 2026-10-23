import IdentityTesting.CountableLowerApproximation
import IdentityTesting.PoolingReverseTests
import IdentityTesting.MomentLowerBound

/-! The actual finite moment-prior obstruction transferred to arbitrary
countable reference laws, including alternatives outside finite support. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem no_identityTest_countable_overlap_moment (q : DiscreteLaw) (δ : ℝ)
    (hδ : 0 < δ) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 : ℝ) / 2000 / overlapMoment q δ) :
    ¬ HasIdentityTest q (1 - δ) n := by
  intro htest
  have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < δ :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hδ)
  obtain ⟨m, hsmall, hrecip⟩ :=
    (hsmall.and (eventually_overlapMoment_reciprocal_prefixPooled_minus_ge_half q hδ)).exists
  have hcompare : (1 : ℝ) / 2000 / overlapMoment q δ ≤
      (1 : ℝ) / 1000 / overlapMoment (prefixPooledLaw q m)
        (δ - residualMass q (Finset.range m)) := by
    have h := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 1 / 1000)
    convert h using 1 <;> ring
  have hno := no_identityTest_of_overlap_moment (prefixPooledFinite q m)
    (δ - residualMass q (Finset.range m)) (sub_pos.mpr hsmall) n (by
      rw [extendFiniteLaw_prefixPooledFinite]
      exact hn.trans hcompare)
  apply hno
  rw [extendFiniteLaw_prefixPooledFinite]
  have ht := hasIdentityTest_prefixPooled_of_countable q m (1 - δ) n htest
  have hrad : 1 - (δ - residualMass q (Finset.range m)) =
      (1 - δ) + residualMass q (Finset.range m) := by ring
  rwa [hrad]

theorem moment_branch_lower (q : DiscreteLaw) (ε : ℝ)
    (_hε0 : 0 < ε) (hε1 : ε < 1) (hcap : largestMass q ≤ 3 / 4)
    (hbranch : 1 - ε < largestMass q / 2) (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / 4000 : ℝ) * (roundedScale q ε : ℝ) ≤ n := by
  have hδ : 0 < 1 - ε := sub_pos.mpr hε1
  have hnroot : (1 / 2000 : ℝ) * (1 / overlapMoment q (1 - ε)) < n := by
    have h : (1 : ℝ) / 2000 / overlapMoment q (1 - ε) < n :=
      lt_of_not_ge (fun hn => no_identityTest_countable_overlap_moment q (1 - ε) hδ n hn
        (by simpa only [sub_sub_cancel] using htest))
    simpa only [div_eq_mul_inv, one_mul] using h
  have hnzero : n ≠ 0 := by
    intro hn
    subst n
    exact no_zero_sample_test q ε hε1 htest
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnzero
  have hscale : complexityScale q ε = 1 / overlapMoment q (1 - ε) := by
    have hpoint : largestMass q ≠ 1 := ne_of_lt (hcap.trans_lt (by norm_num))
    simp only [complexityScale, ne_of_lt hε1, hpoint, not_lt.mpr hcap,
      not_le.mpr hbranch, if_false]
  have hround : (roundedScale q ε : ℝ) < 1 / overlapMoment q (1 - ε) + 1 := by
    unfold roundedScale
    rw [hscale]
    exact Nat.ceil_lt_add_one (one_div_pos.mpr (overlapMoment_pos q hδ)).le
  nlinarith only [hnroot, hn1, hround]

end IdentityTesting
