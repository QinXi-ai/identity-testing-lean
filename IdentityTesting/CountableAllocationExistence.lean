import IdentityTesting.CountableAllocation
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Compact

/-!
# Existence of an actual countable allocation maximizer

The original feasible set is closed in the product topology: nonnegative
allocations have total mass at most one exactly when all finite partial sums do.
It lies in the compact product of unit intervals.  The objective is continuous
there by summable domination by the given weights.
-/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocationFeasible_iff_partialSums (u : ℕ → ℝ) :
    AllocationFeasible u ↔
      (∀ i, 0 ≤ u i) ∧ ∀ s : Finset ℕ, ∑ i ∈ s, u i ≤ 1 := by
  constructor
  · rintro ⟨hu, hsum, htotal⟩
    refine ⟨hu, fun s => ?_⟩
    exact (hsum.sum_le_tsum s (fun i _ => hu i)).trans htotal
  · rintro ⟨hu, hpartial⟩
    have hsum : Summable u := summable_of_sum_le hu hpartial
    exact ⟨hu, hsum, hsum.tsum_le_of_sum_le hpartial⟩

theorem allocationFeasible_coordinate_le_one {u : ℕ → ℝ}
    (hu : AllocationFeasible u) (i : ℕ) : u i ≤ 1 := by
  simpa using (allocationFeasible_iff_partialSums u).mp hu |>.2 {i}

theorem isClosed_allocationFeasible : IsClosed {u : ℕ → ℝ | AllocationFeasible u} := by
  have heq : {u : ℕ → ℝ | AllocationFeasible u} =
      (⋂ i : ℕ, {u : ℕ → ℝ | 0 ≤ u i}) ∩
      (⋂ s : Finset ℕ, {u : ℕ → ℝ | ∑ i ∈ s, u i ≤ 1}) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact allocationFeasible_iff_partialSums u
  rw [heq]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter ?_
  apply isClosed_iInter
  intro s
  exact isClosed_le (continuous_finset_sum s (fun i _ => continuous_apply i)) continuous_const

theorem isCompact_allocationFeasible : IsCompact {u : ℕ → ℝ | AllocationFeasible u} := by
  have hbox : IsCompact {u : ℕ → ℝ | ∀ i, u i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  apply hbox.of_isClosed_subset isClosed_allocationFeasible
  intro u hu i
  exact ⟨hu.1 i, allocationFeasible_coordinate_le_one hu i⟩

theorem continuousOn_countableAllocation_term {a t : ℝ} (ha : 0 ≤ a)
    (ht : 0 < t) (i : ℕ) :
    ContinuousOn (fun u : ℕ → ℝ =>
      a * (u i / (u i + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ))
      {u | AllocationFeasible u} := by
  by_cases hz : a = 0
  · simp only [hz, zero_mul]
    exact continuousOn_const
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hcoord : ContinuousOn (fun u : ℕ → ℝ => u i) {u | AllocationFeasible u} :=
      (continuous_apply i).continuousOn
    have hdiv : ContinuousOn (fun u : ℕ → ℝ => u i / (u i + t ^ 2 * a ^ 2))
        {u | AllocationFeasible u} := by
      apply hcoord.div (hcoord.add continuousOn_const)
      intro u hu
      have hpos : 0 < t ^ 2 * a ^ 2 := by positivity
      exact ne_of_gt (add_pos_of_nonneg_of_pos (hu.1 i) hpos)
    exact continuousOn_const.mul (hdiv.rpow_const (fun _ _ => Or.inr (by norm_num)))

theorem continuousOn_countableAllocationObjective {a : ℕ → ℝ} {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (ht : 0 < t) :
    ContinuousOn (countableAllocationObjective a t) {u | AllocationFeasible u} := by
  unfold countableAllocationObjective
  apply continuousOn_tsum (fun i => continuousOn_countableAllocation_term (ha i) ht i) hasum
  intro i u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (allocation_term_bounds (ha i) (hu.1 i)).1]
  exact (allocation_term_bounds (ha i) (hu.1 i)).2

/-- An actual feasible allocation attains the global maximum of the original
countable objective; compactness and continuity are proved above, not assumed. -/
theorem exists_countableAllocation_maximizer {a : ℕ → ℝ} {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (ht : 0 < t) :
    ∃ u, AllocationFeasible u ∧ ∀ v, AllocationFeasible v →
      countableAllocationObjective a t v ≤ countableAllocationObjective a t u := by
  exact isCompact_allocationFeasible.exists_isMaxOn
    ⟨fun _ => 0, zero_allocation_feasible⟩
    (continuousOn_countableAllocationObjective ha hasum ht)

/-- The supremum in `allocationD` is the value of an actual feasible allocation. -/
theorem allocationD_attained {a : ℕ → ℝ} {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (ht : 0 < t) :
    ∃ u, AllocationFeasible u ∧ countableAllocationObjective a t u = allocationD a t := by
  obtain ⟨u, hu, hmax⟩ := exists_countableAllocation_maximizer ha hasum ht
  refine ⟨u, hu, le_antisymm (countableAllocationObjective_le_allocationD t ha hasum hu) ?_⟩
  apply csSup_le (allocation_values_nonempty a t)
  rintro v ⟨w, hw, rfl⟩
  exact hmax w hw

end IdentityTesting
