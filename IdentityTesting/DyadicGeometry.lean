import IdentityTesting.GeneralAllocationBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual dyadic cell indices for positive finite masses. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical

def dyadicUpper (b : ℝ) (j : ℕ) : ℝ := b * (1 / 2 : ℝ) ^ j

theorem dyadicUpper_pos {b : ℝ} (hb : 0 < b) (j : ℕ) : 0 < dyadicUpper b j :=
  mul_pos hb (pow_pos (by norm_num) j)

theorem exists_dyadic_cell {b a : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ j : ℕ, dyadicUpper b j / 2 < a ∧ a ≤ dyadicUpper b j := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ha hb)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hex : ∃ n : ℕ, dyadicUpper b n < a := by
    refine ⟨N, ?_⟩
    have h := (lt_div_iff₀ hb).mp hN
    simpa only [dyadicUpper, mul_comm] using h
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h := Nat.find_spec hex
    simp only [h0, dyadicUpper, pow_zero, mul_one] at h
    exact (not_lt_of_ge hab) h
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨j, ?_, ?_⟩
  · have h := Nat.find_spec hex
    rw [hj] at h
    simpa only [dyadicUpper, pow_succ, div_eq_mul_inv, one_div, one_mul, mul_assoc] using h
  · have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    exact le_of_not_gt hmin

def dyadicIndex (b a : ℝ) (ha : 0 < a) (hab : a ≤ b) : ℕ :=
  Classical.choose (exists_dyadic_cell ha hab)

theorem dyadicIndex_spec (b a : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    dyadicUpper b (dyadicIndex b a ha hab) / 2 < a ∧
      a ≤ dyadicUpper b (dyadicIndex b a ha hab) :=
  Classical.choose_spec (exists_dyadic_cell ha hab)

theorem sum_dyadicUpper_le {b : ℝ} (hb : 0 ≤ b) (s : Finset ℕ) :
    (∑ j ∈ s, dyadicUpper b j) ≤ 2 * b := by
  have hg := hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hs : HasSum (dyadicUpper b) (2 * b) := by
    convert hg.mul_left b using 1
    norm_num [dyadicUpper]
    ring
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum s (fun j _ => mul_nonneg hb (pow_nonneg (by norm_num) j))

variable {ι : Type*} [Fintype ι]

/-- The weighted cell endpoint moment equals the sum of per-atom endpoint
weights. This is a finite partition identity, not an independence assumption. -/
theorem cell_moment_eq_atom_sum (a : ι → ℝ) (j : ι → ℕ) (b : ℝ) :
    (∑ l ∈ Finset.univ.image j,
      (∑ i, if j i = l then a i else 0) * Real.sqrt (dyadicUpper b l)) =
      ∑ i, a i * Real.sqrt (dyadicUpper b (j i)) := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq_of_mem]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Actual cell endpoints from dyadicIndex give the manuscript factor sqrt(2). -/
theorem dyadic_atom_moment_bounds (a : ι → ℝ) (b : ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b) :
    let j := fun i => dyadicIndex b (a i) (ha i) (hab i)
    let A := ∑ i, (a i) ^ ((3 : ℝ) / 2)
    A ≤ ∑ i, a i * Real.sqrt (dyadicUpper b (j i)) ∧
      (∑ i, a i * Real.sqrt (dyadicUpper b (j i))) ≤ Real.sqrt 2 * A := by
  dsimp only
  constructor
  · apply Finset.sum_le_sum
    intro i _
    rw [allocation_three_halves_eq (ha i).le]
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (dyadicIndex_spec b (a i) (ha i) (hab i)).2) (ha i).le
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [allocation_three_halves_eq (ha i).le]
    have hu : dyadicUpper b (dyadicIndex b (a i) (ha i) (hab i)) ≤ 2 * a i := by
      have h := (dyadicIndex_spec b (a i) (ha i) (hab i)).1
      linarith
    have hroot := Real.sqrt_le_sqrt hu
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hroot
    have h := mul_le_mul_of_nonneg_left hroot (ha i).le
    nlinarith only [h]

end IdentityTesting.EmpiricalSeeds
