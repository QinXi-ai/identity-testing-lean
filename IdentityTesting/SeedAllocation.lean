import IdentityTesting.EmpiricalSeeds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-! Explicit integer seed allocation and its overlap/collision cost bounds. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def seedMoment (r u : ι → ℝ) : ℝ := ∑ i, r i * Real.sqrt (u i)

def allocatedSeedCount (c : ℝ) (r u : ι → ℝ) (i : ι) : ℕ :=
  ⌈c * seedMoment r u * r i / Real.sqrt (u i)⌉₊

theorem seedMoment_pos {r u : ι → ℝ} (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i) :
    0 < seedMoment r u := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (hr i) (Real.sqrt_pos.2 (hu i))
  · exact Finset.univ_nonempty

theorem allocatedSeedCount_pos {c : ℝ} {r u : ι → ℝ} (hc : 0 < c)
    (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i) (i : ι) :
    0 < allocatedSeedCount c r u i := by
  apply Nat.ceil_pos.2
  exact div_pos (mul_pos (mul_pos hc (seedMoment_pos hr hu)) (hr i))
    (Real.sqrt_pos.2 (hu i))

/-- Rounding up uses at most one additional support label per cell. -/
theorem allocatedSeedCount_overlap_bound {c : ℝ} {r u : ι → ℝ} (hc : 0 < c)
    (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i) :
    (∑ i, (allocatedSeedCount c r u i : ℝ) * u i) ≤
      c * (seedMoment r u) ^ 2 + ∑ i, u i := by
  have hA := seedMoment_pos hr hu
  calc
    (∑ i, (allocatedSeedCount c r u i : ℝ) * u i) ≤
        ∑ i, (c * seedMoment r u * r i / Real.sqrt (u i) + 1) * u i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (hu i).le
      exact (Nat.ceil_lt_add_one
        (div_nonneg (mul_nonneg (mul_nonneg hc.le hA.le) (hr i).le)
          (Real.sqrt_nonneg _))).le
    _ = ∑ i, (c * seedMoment r u * (r i * Real.sqrt (u i)) + u i) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (c * seedMoment r u * r i / Real.sqrt (u i) + 1) * u i =
            c * seedMoment r u * r i * (u i / Real.sqrt (u i)) + u i := by ring
        _ = c * seedMoment r u * (r i * Real.sqrt (u i)) + u i := by
          rw [Real.div_sqrt]
          ring
    _ = c * (seedMoment r u) ^ 2 + ∑ i, u i := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      change c * seedMoment r u * seedMoment r u + _ = _
      ring

/-- The allocated number of seeds controls the latent collision coefficient. -/
theorem allocatedSeedCount_collision_bound {c : ℝ} {r u : ι → ℝ} (hc : 0 < c)
    (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i) :
    (∑ i, r i ^ 2 / (allocatedSeedCount c r u i : ℝ)) ≤ 1 / c := by
  have hA := seedMoment_pos hr hu
  calc
    (∑ i, r i ^ 2 / (allocatedSeedCount c r u i : ℝ)) ≤
        ∑ i, r i * Real.sqrt (u i) / (c * seedMoment r u) := by
      apply Finset.sum_le_sum
      intro i _
      have hs : 0 < Real.sqrt (u i) := Real.sqrt_pos.2 (hu i)
      have hz : 0 < c * seedMoment r u * r i / Real.sqrt (u i) :=
        div_pos (mul_pos (mul_pos hc hA) (hr i)) hs
      calc
        r i ^ 2 / (allocatedSeedCount c r u i : ℝ) ≤
            r i ^ 2 / (c * seedMoment r u * r i / Real.sqrt (u i)) :=
          div_le_div_of_nonneg_left (sq_nonneg _) hz (Nat.le_ceil _)
        _ = r i * Real.sqrt (u i) / (c * seedMoment r u) := by
          field_simp [hc.ne', hA.ne', (hr i).ne', hs.ne']
    _ = seedMoment r u / (c * seedMoment r u) := by rw [← Finset.sum_div]; rfl
    _ = 1 / c := by field_simp [hc.ne', hA.ne']

theorem allocatedSeedCount_scaled_collision_bound {c : ℝ} {r u : ι → ℝ}
    (hc : 0 < c) (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i) (f : ℝ) :
    (∑ i, (f * r i) ^ 2 / (allocatedSeedCount c r u i : ℝ)) ≤ f ^ 2 / c := by
  calc
    (∑ i, (f * r i) ^ 2 / (allocatedSeedCount c r u i : ℝ)) =
        f ^ 2 * ∑ i, r i ^ 2 / (allocatedSeedCount c r u i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ f ^ 2 * (1 / c) :=
      mul_le_mul_of_nonneg_left (allocatedSeedCount_collision_bound hc hr hu) (sq_nonneg f)
    _ = f ^ 2 / c := by ring

/-- With the manuscript choice c=B*n^2, the actual union-bound coefficient is
at most f^2/(2B); the cell weights need not have independent observed counts. -/
theorem allocatedSeedCount_sample_collision_bound {B : ℝ} {r u : ι → ℝ}
    (hB : 0 < B) (hr : ∀ i, 0 < r i) (hu : ∀ i, 0 < u i)
    (n : ℕ) (hn : 0 < n) (f : ℝ) :
    (n.choose 2 : ℝ) *
      (∑ i, (f * r i) ^ 2 / (allocatedSeedCount (B * (n : ℝ) ^ 2) r u i : ℝ)) ≤
      f ^ 2 / (2 * B) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hc : 0 < B * (n : ℝ) ^ 2 := mul_pos hB (sq_pos_of_pos hnR)
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    simpa using (Nat.choose_le_pow_div (α := ℝ) 2 n)
  calc
    _ ≤ (n.choose 2 : ℝ) * (f ^ 2 / (B * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (allocatedSeedCount_scaled_collision_bound hc hr hu f)
        (Nat.cast_nonneg _)
    _ ≤ ((n : ℝ) ^ 2 / 2) * (f ^ 2 / (B * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hchoose (div_nonneg (sq_nonneg _) hc.le)
    _ = f ^ 2 / (2 * B) := by field_simp [hB.ne', hnR.ne']

end IdentityTesting.EmpiricalSeeds
