import IdentityTesting.DyadicSeedLowerBound

/-! The explicit dyadic partition and ceiling allocation retained in the seed interface. -/
noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem exists_dyadic_seed_counts_with_formula (a : ι → ℝ) (b : ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ∃ (j : ι → ℕ) (m : OccupiedCells j → ℕ),
      (∀ i, j i = dyadicIndex b (a i) (ha i) (hab i)) ∧
      (∀ l, m l = allocatedSeedCount (B * (n : ℝ) ^ 2) (cellMass a j)
        (fun l : OccupiedCells j => dyadicUpper b l.val) l) ∧
      (∀ i, dyadicUpper b (j i) / 2 < a i ∧ a i ≤ dyadicUpper b (j i)) ∧
      (∀ l, 0 < m l) ∧
      (∑ l, (m l : ℝ) * dyadicUpper b l.val) ≤
        2 * B * (n : ℝ) ^ 2 * (∑ i, (a i) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b ∧
      (n.choose 2 : ℝ) * (∑ l, (cellMass a j l) ^ 2 / (m l : ℝ)) ≤ 1 / (2 * B) := by
  let j := fun i => dyadicIndex b (a i) (ha i) (hab i)
  let r := cellMass a j
  let u := fun l : OccupiedCells j => dyadicUpper b l.val
  let c := B * (n : ℝ) ^ 2
  let m := allocatedSeedCount c r u
  have hb : 0 < b := (ha (Classical.arbitrary ι)).trans_le (hab _)
  have hr : ∀ l, 0 < r l := cellMass_pos ha j
  have hu : ∀ l, 0 < u l := fun l => dyadicUpper_pos hb l.val
  have hc : 0 < c := mul_pos hB (sq_pos_of_pos (Nat.cast_pos.mpr hn))
  have hm : ∀ l, 0 < m l := allocatedSeedCount_pos hc hr hu
  refine ⟨j, m, (fun _ => rfl), (fun _ => rfl),
    (fun i => dyadicIndex_spec b (a i) (ha i) (hab i)), hm, ?_, ?_⟩
  · have hmoment : seedMoment r u ≤ Real.sqrt 2 * ∑ i, (a i) ^ ((3 : ℝ) / 2) := by
      rw [cell_seedMoment_eq]
      exact (dyadic_atom_moment_bounds a b ha hab).2
    have hA : 0 ≤ ∑ i, (a i) ^ ((3 : ℝ) / 2) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (ha i).le _)
    have hsq := (sq_le_sq₀ (seedMoment_pos hr hu).le
      (mul_nonneg (Real.sqrt_nonneg _) hA)).mpr hmoment
    have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [mul_pow, hsqrt] at hsq
    calc
      _ ≤ c * (seedMoment r u) ^ 2 + ∑ l, u l := allocatedSeedCount_overlap_bound hc hr hu
      _ ≤ c * (2 * (∑ i, (a i) ^ ((3 : ℝ) / 2)) ^ 2) + 2 * b :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hc.le) (sum_cellUpper_le j hb.le)
      _ = _ := by dsimp only [c]; ring
  · simpa only [one_mul, one_pow] using allocatedSeedCount_sample_collision_bound hB hr hu n hn 1

end IdentityTesting.EmpiricalSeeds
