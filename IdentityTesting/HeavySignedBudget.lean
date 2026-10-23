import IdentityTesting.HeavySignedFamily
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Actual diagonal and rank-one size bounds from the tail allocation budget -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavySignedBudget

open HeavySignedFamily

variable {k : ℕ}

def diagonalEnergy (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ) : ℝ :=
  ∑ i, (a i ^ 2 / q.mass i.succ) ^ 2

def rankVariance (a : Fin k → ℝ) : ℝ := ∑ i, a i ^ 2

theorem diagonalEnergy_nonneg (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ) :
    0 ≤ diagonalEnergy q a := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem rankVariance_nonneg (a : Fin k → ℝ) : 0 ≤ rankVariance a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem rankVariance_sq_le (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) :
    (rankVariance a) ^ 2 ≤ diagonalEnergy q a * (tailTotal q) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset (Fin k))
    (r := fun i => a i ^ 2) (f := fun i => (a i ^ 2 / q.mass i.succ) ^ 2)
    (g := fun i => (q.mass i.succ) ^ 2)
    (fun i _ => sq_nonneg _) (fun i _ => sq_nonneg _) ?_
  · have hqsum := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun i : Fin k => q.mass i.succ) (fun i _ => (hq i.succ).le)
    exact hcs.trans (mul_le_mul_of_nonneg_left hqsum (diagonalEnergy_nonneg q a))
  · intro i _
    field_simp [ne_of_gt (hq i.succ)]

theorem rankVariance_head_bound (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hR : tailTotal q ≤ (1 : ℝ) / 4) :
    (rankVariance a) ^ 2 / (q.mass 0) ^ 2 ≤ diagonalEnergy q a / 9 := by
  apply (div_le_div_iff₀ (sq_pos_of_pos (hq 0)) (by norm_num : (0 : ℝ) < 9)).2
  have htotal := reference_head_tail q
  have hR0 : 0 ≤ tailTotal q := Finset.sum_nonneg (fun i _ => (hq i.succ).le)
  have hscale : 3 * tailTotal q ≤ q.mass 0 := by linarith only [htotal, hR]
  have hscale2 := pow_le_pow_left₀ (mul_nonneg (by norm_num) hR0) hscale 2
  have hscaled := mul_le_mul_of_nonneg_left hscale2 (diagonalEnergy_nonneg q a)
  have hcs := rankVariance_sq_le q a hq
  nlinarith only [hscaled, hcs]

theorem allocation_diagonalEnergy_bound
    (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    diagonalEnergy q (allocationAmplitude q x) ≤ 256 / T ^ 2 := by
  have hraw (i : Fin k) : (q.mass i.succ) ^ 2 * (x i) ^ 4 ≤
      (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    apply (le_div_iff₀ (sub_pos.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2))).2
    nlinarith only [mul_nonneg (sq_nonneg (q.mass i.succ)) (sq_nonneg ((x i) ^ 4))]
  have hi : ∀ i : Fin k,
      ((allocationAmplitude q x i) ^ 2 / q.mass i.succ) ^ 2 ≤
        256 * ((q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) := by
    intro i
    unfold allocationAmplitude
    split_ifs
    · calc
        _ = 256 * ((q.mass i.succ) ^ 2 * (x i) ^ 4) := by
          field_simp [ne_of_gt (hq i.succ)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hraw i) (by norm_num)
    · norm_num only [zero_pow, zero_div]
      exact mul_nonneg (by norm_num) (div_nonneg (by positivity)
        (sub_nonneg.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2).le))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hi i)
  rw [← Finset.mul_sum] at hsum
  apply (le_div_iff₀ (sq_pos_of_pos hT)).2
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg T)
  unfold diagonalEnergy
  nlinarith only [hscaled, hbudget]

end IdentityTesting.HeavySignedBudget
