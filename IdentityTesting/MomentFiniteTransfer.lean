import IdentityTesting.MomentUpperBound
import IdentityTesting.PoolingTests
import IdentityTesting.LargestAtom

/-! The finite moment tester acts on the original countable observation alphabet;
all labels outside the reference support are retained as one pooled label. -/
noncomputable section
namespace IdentityTesting.MomentTesting
open scoped BigOperators
open Classical FiniteTesting EventCounts

theorem residualMass_eq_zero_of_supported (q : DiscreteLaw) (s : Finset ℕ)
    (hq : ∀ i, i ∉ s → q.mass i = 0) : residualMass q s = 0 := by
  unfold residualMass
  calc
    _ = ∑' i : {i : ℕ // i ∉ s}, (0 : ℝ) := tsum_congr (fun i => hq i.val i.property)
    _ = 0 := tsum_zero

theorem finiteOverlapMoment_pooled_of_supported (q : DiscreteLaw) (s : Finset ℕ)
    (hq : ∀ i, i ∉ s → q.mass i = 0) (δ : ℝ) :
    finiteOverlapMoment (pooledLaw q s) δ = overlapMoment q δ := by
  have hr := residualMass_eq_zero_of_supported q s hq
  have hsum : overlapMoment q δ =
      ∑ i ∈ s, min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) := by
    unfold overlapMoment
    apply tsum_eq_sum
    intro i hi
    rw [hq i hi]
    norm_num
  rw [hsum, finiteOverlapMoment, Fintype.sum_option]
  change min (residualMass q s) ((residualMass q s) ^ ((3 : ℝ) / 2) / Real.sqrt δ) +
      (∑ i : s, min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ)) = _
  rw [hr]
  norm_num only [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0), zero_div, min_self, zero_add]
  exact Finset.sum_coe_sort s (fun i => min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ))

theorem hasIdentityTest_moment_of_finite_support_sharp (q : DiscreteLaw) (s : Finset ℕ)
    (hq : ∀ i, i ∉ s → q.mass i = 0) (δ : ℝ) (hδ : 0 < δ)
    (hhead : 2 * δ ≤ largestMass q) :
    ∃ n : ℕ, HasIdentityTest q (1 - δ) n ∧
      (n : ℝ) ≤ 50000000000001 / overlapMoment q δ := by
  classical
  have hr := residualMass_eq_zero_of_supported q s hq
  have hj : largestIndex q ∈ s := by
    by_contra hj
    have hz := hq (largestIndex q) hj
    rw [largestMass_eq_selected, hz] at hhead
    linarith
  let y : PoolLabel s := some ⟨largestIndex q, hj⟩
  have hy : (pooledLaw q s).mass y = largestMass q := (largestMass_eq_selected q).symm
  have hyH : y ∈ heavyLabels (pooledLaw q s) δ := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hy]
    linarith
  have hv : 2 * δ ≤ eventMass (pooledLaw q s) (heavyLabels (pooledLaw q s) δ) := by
    have h := Finset.single_le_sum (s := heavyLabels (pooledLaw q s) δ)
      (f := (pooledLaw q s).mass) (fun i _ => (pooledLaw q s).nonneg i) hyH
    rw [hy] at h
    exact hhead.trans h
  obtain ⟨n, test, hnull, halt, hn⟩ := finite_moment_identity_test_sharp (pooledLaw q s) δ hδ hv
  refine ⟨n, hasIdentityTest_of_pooled_test q s (1 - δ) n test hnull ?_, ?_⟩
  · simpa only [hr, sub_zero] using halt
  · rw [finiteOverlapMoment_pooled_of_supported q s hq δ] at hn
    exact hn

theorem hasIdentityTest_moment_of_finite_support (q : DiscreteLaw) (s : Finset ℕ)
    (hq : ∀ i, i ∉ s → q.mass i = 0) (δ : ℝ) (hδ : 0 < δ)
    (hhead : 2 * δ ≤ largestMass q) :
    ∃ n : ℕ, HasIdentityTest q (1 - δ) n ∧
      (n : ℝ) ≤ 100000000000000 / overlapMoment q δ := by
  obtain ⟨n, hn, hb⟩ := hasIdentityTest_moment_of_finite_support_sharp q s hq δ hδ hhead
  exact ⟨n, hn, hb.trans (div_le_div_of_nonneg_right (by norm_num)
    (overlapMoment_pos q hδ).le)⟩

end IdentityTesting.MomentTesting
