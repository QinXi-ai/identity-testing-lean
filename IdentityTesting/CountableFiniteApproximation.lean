import IdentityTesting.CountableAllocationApproximation
import IdentityTesting.FiniteEmbedding

/-! Actual normalized finite coarsenings on the original natural-number alphabet.
The prefix labels are unchanged and the residual is assigned to label m. -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace IdentityTesting

def prefixPooledLaw (q : DiscreteLaw) (m : ℕ) : DiscreteLaw where
  mass i := truncatedMass q.mass (Finset.range m) i +
    if i = m then residualMass q (Finset.range m) else 0
  nonneg i := add_nonneg (truncatedMass_nonneg q.nonneg _ i) (by
    split_ifs
    · exact tsum_nonneg (fun i => q.nonneg i)
    · exact le_rfl)
  summable := (truncatedMass_summable q.mass (Finset.range m)).add
    (hasSum_ite_eq m (residualMass q (Finset.range m))).summable
  total := by
    rw [(truncatedMass_summable q.mass (Finset.range m)).tsum_add
      (hasSum_ite_eq m (residualMass q (Finset.range m))).summable,
      (hasSum_ite_eq m (residualMass q (Finset.range m))).tsum_eq]
    have hp : (∑' i, truncatedMass q.mass (Finset.range m) i) =
        ∑ i ∈ Finset.range m, q.mass i := by
      rw [tsum_eq_sum (s := Finset.range m) (fun i hi => by simp [truncatedMass, hi])]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [truncatedMass, if_pos hi]
    rw [hp]
    exact q.summable.sum_add_tsum_compl.trans q.total

theorem prefixPooledLaw_mass_of_lt (q : DiscreteLaw) (m i : ℕ) (hi : i < m) :
    (prefixPooledLaw q m).mass i = q.mass i := by
  simp [prefixPooledLaw, truncatedMass, Finset.mem_range, hi, ne_of_lt hi]

@[simp] theorem prefixPooledLaw_mass_residual (q : DiscreteLaw) (m : ℕ) :
    (prefixPooledLaw q m).mass m = residualMass q (Finset.range m) := by
  simp [prefixPooledLaw, truncatedMass]

theorem prefixPooledLaw_mass_zero (q : DiscreteLaw) (m i : ℕ) (hi : m + 1 ≤ i) :
    (prefixPooledLaw q m).mass i = 0 := by
  have hnot : ¬ i < m := by omega
  have hne : i ≠ m := by omega
  simp [prefixPooledLaw, truncatedMass, Finset.mem_range, hnot, hne]

/-- The actual finite probability vector whose zero extension is this law. -/
def prefixPooledFinite (q : DiscreteLaw) (m : ℕ) : FiniteTesting.Probability (Fin (m + 1)) where
  mass i := (prefixPooledLaw q m).mass i.val
  nonneg i := (prefixPooledLaw q m).nonneg i.val
  total := by
    have hs : (∑' i, (prefixPooledLaw q m).mass i) =
        ∑ i ∈ Finset.range (m + 1), (prefixPooledLaw q m).mass i :=
      tsum_eq_sum (s := Finset.range (m + 1))
        (fun i hi => prefixPooledLaw_mass_zero q m i (Nat.le_of_not_gt (by
          simpa only [Finset.mem_range] using hi)))
    exact (Fin.sum_univ_eq_sum_range (prefixPooledLaw q m).mass (m + 1)).trans
      (hs.symm.trans (prefixPooledLaw q m).total)

private theorem discreteLaw_ext {p q : DiscreteLaw} (h : ∀ i, p.mass i = q.mass i) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

/-- This is a constructed finite reference on ℕ, not a finite-support certificate
provided as an extra premise. -/
theorem extendFiniteLaw_prefixPooledFinite (q : DiscreteLaw) (m : ℕ) :
    extendFiniteLaw (prefixPooledFinite q m) = prefixPooledLaw q m := by
  apply discreteLaw_ext
  intro i
  by_cases hi : i < m + 1
  · exact extendFiniteLaw_mass_val (prefixPooledFinite q m) ⟨i, hi⟩
  · rw [extendFiniteLaw_mass_of_not_lt _ i hi,
      prefixPooledLaw_mass_zero q m i (Nat.le_of_not_gt hi)]

theorem prefixPooledLaw_discardedMass (q : DiscreteLaw) (m : ℕ) :
    discardedMass (prefixPooledLaw q m).mass (Finset.range m) =
      residualMass q (Finset.range m) := by
  have hp := (prefixPooledLaw q m).summable.sum_add_tsum_compl (s := Finset.range m)
  have hq := q.summable.sum_add_tsum_compl (s := Finset.range m)
  rw [(prefixPooledLaw q m).total] at hp
  rw [q.total] at hq
  have heq : (∑ i ∈ Finset.range m, (prefixPooledLaw q m).mass i) =
      ∑ i ∈ Finset.range m, q.mass i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp hi)
  rw [heq] at hp
  change (∑ i ∈ Finset.range m, q.mass i) +
    discardedMass (prefixPooledLaw q m).mass (Finset.range m) = 1 at hp
  change (∑ i ∈ Finset.range m, q.mass i) + residualMass q (Finset.range m) = 1 at hq
  linarith

/-- Uniform in every time t: the actual coarsened reference and original
allocation functions differ by at most the actual residual reference mass. -/
theorem allocationD_prefixPooled_abs_le (q : DiscreteLaw) (m : ℕ) (t : ℝ) :
    |allocationD (prefixPooledLaw q m).mass t - allocationD q.mass t| ≤
      residualMass q (Finset.range m) := by
  apply allocationD_abs_sub_le_tail (Finset.range m) t
    (prefixPooledLaw q m).nonneg (prefixPooledLaw q m).summable q.nonneg q.summable
    (fun i hi => prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp hi))
  · exact (prefixPooledLaw_discardedMass q m).le
  · exact le_rfl

theorem prefixResidual_tendsto_zero (q : DiscreteLaw) :
    Tendsto (fun m => residualMass q (Finset.range m)) atTop (𝓝 0) :=
  discardedMass_prefix_tendsto_zero q.summable

theorem allocationD_prefixPooled_tendsto (q : DiscreteLaw) (t : ℝ) :
    Tendsto (fun m => allocationD (prefixPooledLaw q m).mass t) atTop
      (𝓝 (allocationD q.mass t)) := by
  have habs : Tendsto
      (fun m => |allocationD (prefixPooledLaw q m).mass t - allocationD q.mass t|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun m => allocationD_prefixPooled_abs_le q m t)
      (prefixResidual_tendsto_zero q)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

end IdentityTesting
