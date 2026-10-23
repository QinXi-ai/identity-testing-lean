import IdentityTesting.CountableModel
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem DiscreteLaw.summable_min (p q : DiscreteLaw) :
    Summable (fun i => min (p.mass i) (q.mass i)) :=
  Summable.of_nonneg_of_le (fun i => le_min (p.nonneg i) (q.nonneg i))
    (fun i => min_le_left _ _) p.summable

theorem abs_sub_eq_add_sub_two_min (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem totalVariation_eq_one_sub_overlap (p q : DiscreteLaw) :
    totalVariation p q = 1 - ∑' i, min (p.mass i) (q.mass i) := by
  unfold totalVariation
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [(p.summable.add q.summable).tsum_sub ((p.summable_min q).mul_left 2),
      p.summable.tsum_add q.summable, tsum_mul_left, p.total, q.total]
  ring

def residualMass (p : DiscreteLaw) (s : Finset ℕ) : ℝ :=
  ∑' i : {i : ℕ // i ∉ s}, p.mass i

def residualOverlap (p q : DiscreteLaw) (s : Finset ℕ) : ℝ :=
  ∑' i : {i : ℕ // i ∉ s}, min (p.mass i) (q.mass i)

/-- The TV expression for retaining labels in s and pooling their complement.
The probability-law pushforward connection is a separate formalization obligation. -/
def pooledTVFormula (p q : DiscreteLaw) (s : Finset ℕ) : ℝ :=
  1 - ((∑ i ∈ s, min (p.mass i) (q.mass i)) +
    min (residualMass p s) (residualMass q s))

theorem residualOverlap_nonneg (p q : DiscreteLaw) (s : Finset ℕ) :
    0 ≤ residualOverlap p q s :=
  tsum_nonneg (fun i => le_min (p.nonneg i) (q.nonneg i))

theorem overlap_split (p q : DiscreteLaw) (s : Finset ℕ) :
    (∑ i ∈ s, min (p.mass i) (q.mass i)) + residualOverlap p q s =
    ∑' i, min (p.mass i) (q.mass i) := by
  exact (p.summable_min q).sum_add_tsum_compl

theorem pooledTV_loss_le_reference_tail (p q : DiscreteLaw) (s : Finset ℕ) :
    totalVariation p q - pooledTVFormula p q s ≤ residualMass q s := by
  rw [totalVariation_eq_one_sub_overlap, ← overlap_split p q s]
  unfold pooledTVFormula
  have h := min_le_right (residualMass p s) (residualMass q s)
  have hnonneg := residualOverlap_nonneg p q s
  linarith

theorem strict_alternative_survives_pooling_formula
    (p q : DiscreteLaw) (s : Finset ℕ) (ε : ℝ)
    (h : ε < totalVariation p q) :
    ε - residualMass q s < pooledTVFormula p q s := by
  have hbound := pooledTV_loss_le_reference_tail p q s
  linarith

end IdentityTesting
