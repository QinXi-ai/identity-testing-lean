import IdentityTesting.CountableAllocation
import IdentityTesting.CountableOverlap
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Finite truncation bounds for the original countable allocation supremum.
The feasible allocations and the Target allocationD are unchanged. -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace IdentityTesting

def truncatedMass (a : ℕ → ℝ) (s : Finset ℕ) (i : ℕ) : ℝ :=
  if i ∈ s then a i else 0

def discardedMass (a : ℕ → ℝ) (s : Finset ℕ) : ℝ :=
  ∑' i : {i : ℕ // i ∉ s}, a i

theorem truncatedMass_nonneg {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (s : Finset ℕ) :
    ∀ i, 0 ≤ truncatedMass a s i := by
  intro i
  by_cases hi : i ∈ s <;> simp [truncatedMass, hi, ha i]

theorem truncatedMass_summable (a : ℕ → ℝ) (s : Finset ℕ) :
    Summable (truncatedMass a s) := by
  apply summable_of_ne_finset_zero (s := s)
  intro i hi
  simp only [truncatedMass, if_neg hi]

theorem discardedMass_nonneg {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (s : Finset ℕ) :
    0 ≤ discardedMass a s := tsum_nonneg (fun i => ha i)

theorem countableAllocationObjective_truncated (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ)
    (u : ℕ → ℝ) :
    countableAllocationObjective (truncatedMass a s) t u =
      ∑ i ∈ s, a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ) := by
  unfold countableAllocationObjective
  rw [tsum_eq_sum (s := s) (fun i hi => by simp [truncatedMass, hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [truncatedMass, if_pos hi]

theorem countableAllocationObjective_truncation_bounds {a u : ℕ → ℝ} (s : Finset ℕ) (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hu : ∀ i, 0 ≤ u i) :
    countableAllocationObjective (truncatedMass a s) t u ≤ countableAllocationObjective a t u ∧
      countableAllocationObjective a t u ≤
        countableAllocationObjective (truncatedMass a s) t u + discardedMass a s := by
  have hterm := countableAllocationObjective_summable t ha hasum hu
  constructor
  · apply (countableAllocationObjective_summable t (truncatedMass_nonneg ha s)
      (truncatedMass_summable a s) hu).tsum_le_tsum _ hterm
    intro i
    by_cases hi : i ∈ s
    · simp only [truncatedMass, if_pos hi]
      exact le_rfl
    · simpa only [truncatedMass, if_neg hi, zero_mul] using (allocation_term_bounds (ha i) (hu i)).1
  · have hsplit := hterm.sum_add_tsum_compl (s := s)
    have htail :
        (∑' i : {i : ℕ // i ∉ s},
          a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) ≤ discardedMass a s := by
      exact (hterm.subtype {i | i ∉ s}).tsum_le_tsum
        (fun i => (allocation_term_bounds (ha i) (hu i)).2) (hasum.subtype {i | i ∉ s})
    rw [countableAllocationObjective_truncated]
    change (∑' i, a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) ≤ _
    exact hsplit.symm.le.trans (add_le_add_left htail _)

/-- Exact manuscript truncation interval for the actual original supremum. -/
theorem allocationD_truncation_bounds {a : ℕ → ℝ} (s : Finset ℕ) (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    allocationD (truncatedMass a s) t ≤ allocationD a t ∧
      allocationD a t ≤ allocationD (truncatedMass a s) t + discardedMass a s := by
  constructor
  · apply csSup_le (allocation_values_nonempty (truncatedMass a s) t)
    rintro v ⟨u, hu, rfl⟩
    exact (countableAllocationObjective_truncation_bounds s t ha hasum hu.1).1.trans
      (countableAllocationObjective_le_allocationD t ha hasum hu)
  · apply csSup_le (allocation_values_nonempty a t)
    rintro v ⟨u, hu, rfl⟩
    exact (countableAllocationObjective_truncation_bounds s t ha hasum hu.1).2.trans
      (add_le_add_right (countableAllocationObjective_le_allocationD t
        (truncatedMass_nonneg ha s) (truncatedMass_summable a s) hu) _)

/-- Any two nonnegative summable sequences agreeing on a retained finite set
have allocation values differing by at most the larger omitted mass. -/
theorem allocationD_abs_sub_le_tail {a b : ℕ → ℝ} (s : Finset ℕ) (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hb : ∀ i, 0 ≤ b i) (hbsum : Summable b)
    (heq : ∀ i ∈ s, a i = b i) (r : ℝ)
    (har : discardedMass a s ≤ r) (hbr : discardedMass b s ≤ r) :
    |allocationD a t - allocationD b t| ≤ r := by
  have htrunc : truncatedMass a s = truncatedMass b s := by
    funext i
    by_cases hi : i ∈ s
    · simp only [truncatedMass, if_pos hi, heq i hi]
    · simp only [truncatedMass, if_neg hi]
  have hA := allocationD_truncation_bounds s t ha hasum
  have hB := allocationD_truncation_bounds s t hb hbsum
  rw [htrunc] at hA
  rw [abs_le]
  constructor <;> linarith

theorem discardedMass_prefix_tendsto_zero {a : ℕ → ℝ} (hasum : Summable a) :
    Tendsto (fun m : ℕ => discardedMass a (Finset.range m)) atTop (𝓝 0) := by
  have hprefix := hasum.hasSum.tendsto_sum_nat
  have heq (m : ℕ) : discardedMass a (Finset.range m) =
      (∑' i, a i) - ∑ i ∈ Finset.range m, a i := by
    have h := hasum.sum_add_tsum_compl (s := Finset.range m)
    change (∑ i ∈ Finset.range m, a i) + discardedMass a (Finset.range m) = _ at h
    linarith
  have hconst : Tendsto (fun _ : ℕ => ∑' i, a i) atTop (𝓝 (∑' i, a i)) :=
    tendsto_const_nhds
  simpa only [heq, sub_self] using hconst.sub hprefix

end IdentityTesting
