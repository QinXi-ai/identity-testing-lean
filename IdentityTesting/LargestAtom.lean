import IdentityTesting.Target
import IdentityTesting.Endpoints
import Mathlib.Data.Finset.Max

noncomputable section
open scoped BigOperators
open Filter
namespace IdentityTesting

theorem DiscreteLaw.exists_positive (q : DiscreteLaw) : ∃ i, 0 < q.mass i := by
  by_contra h
  have hz : q.mass = fun _ => 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (q.nonneg i)
  have ht := q.total
  rw [hz] at ht
  simp at ht

theorem DiscreteLaw.exists_largest (q : DiscreteLaw) :
    ∃ i, ∀ j, q.mass j ≤ q.mass i := by
  obtain ⟨j, hj⟩ := q.exists_positive
  have hevent : ∀ᶠ i in atTop, q.mass i < q.mass j :=
    q.summable.tendsto_atTop_zero.eventually (gt_mem_nhds hj)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let K := max N (j + 1)
  have hjK : j ∈ Finset.range K := by
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right N (j + 1)))
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.range K) q.mass ⟨j, hjK⟩
  refine ⟨i, fun k => ?_⟩
  by_cases hk : k < K
  · exact hmax k (Finset.mem_range.mpr hk)
  · have hNk : N ≤ k := (le_max_left N (j + 1)).trans (Nat.le_of_not_gt hk)
    exact (hN k hNk).le.trans (hmax j hjK)

theorem largestIndex_spec (q : DiscreteLaw) : ∀ j, q.mass j ≤ q.mass (largestIndex q) := by
  exact Nat.sInf_mem q.exists_largest

theorem largestMass_eq_selected (q : DiscreteLaw) : largestMass q = q.mass (largestIndex q) := by
  unfold largestMass
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty q.mass) (fun y hy => by
      obtain ⟨j, rfl⟩ := hy
      exact largestIndex_spec q j)
  · exact le_csSup ⟨1, by
      rintro y ⟨i, rfl⟩
      exact q.mass_le_one i⟩ ⟨largestIndex q, rfl⟩

theorem largestMass_pos (q : DiscreteLaw) : 0 < largestMass q := by
  obtain ⟨i, hi⟩ := q.exists_positive
  rw [largestMass_eq_selected]
  exact hi.trans_le (largestIndex_spec q i)

theorem largestMass_le_one (q : DiscreteLaw) : largestMass q ≤ 1 := by
  rw [largestMass_eq_selected]
  exact q.mass_le_one _

theorem tailMasses_nonneg (q : DiscreteLaw) (i : ℕ) : 0 ≤ tailMasses q i := by
  unfold tailMasses
  split
  · exact le_rfl
  · exact q.nonneg i

theorem tailMasses_summable (q : DiscreteLaw) : Summable (tailMasses q) := by
  refine Summable.of_nonneg_of_le (tailMasses_nonneg q) (fun i => ?_) q.summable
  unfold tailMasses
  split
  · exact q.nonneg i
  · exact le_rfl

theorem tailMasses_total (q : DiscreteLaw) :
    (∑' i, tailMasses q i) = 1 - largestMass q := by
  have h := q.summable.tsum_eq_add_tsum_ite (largestIndex q)
  change (∑' i, q.mass i) = q.mass (largestIndex q) + (∑' i, tailMasses q i) at h
  rw [q.total, ← largestMass_eq_selected] at h
  linarith

end IdentityTesting
