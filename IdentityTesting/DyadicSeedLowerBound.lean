import IdentityTesting.DyadicCells
import IdentityTesting.SeedSupport

/-! Actual dyadic cells and allocated seeds give statistical lower bounds. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting MultiBinSeeds

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The bin map and every integer seed count are constructed from the atom masses. -/
theorem exists_dyadic_seed_counts (a : ι → ℝ) (b : ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ∃ (j : ι → ℕ) (m : OccupiedCells j → ℕ),
      (∀ i, a i ≤ dyadicUpper b (j i)) ∧ (∀ l, 0 < m l) ∧
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
  refine ⟨j, m, (fun i => (dyadicIndex_spec b (a i) (ha i) (hab i)).2), hm, ?_, ?_⟩
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
      _ ≤ c * (seedMoment r u) ^ 2 + ∑ l, u l :=
        allocatedSeedCount_overlap_bound hc hr hu
      _ ≤ c * (2 * (∑ i, (a i) ^ ((3 : ℝ) / 2)) ^ 2) + 2 * b :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hc.le) (sum_cellUpper_le j hb.le)
      _ = _ := by dsimp only [c]; ring
  · simpa only [one_mul, one_pow] using
      (allocatedSeedCount_sample_collision_bound hB hr hu n hn 1)

/-- A full constructed-prior obstruction in the original countable testing model,
for strictly positive finite reference laws satisfying the dyadic moment bound. -/
theorem no_identityTest_of_dyadic_seeds {k : ℕ} (q : Probability (Fin k))
    (hq : ∀ i, 0 < q.mass i) (b : ℝ) (hqb : ∀ i, q.mass i ≤ b)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (n : ℕ) (hn : 0 < n)
    (hgap : 2 * B * (n : ℝ) ^ 2 * (∑ i, (q.mass i) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b < 1 - ε)
    (hBsample : 1 / (2 * B) < (1 : ℝ) / 3) :
    ¬ IdentityTesting.HasIdentityTest (IdentityTesting.extendFiniteLaw q) ε n := by
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have ht := q.total
    simpa using ht
  letI : NeZero k := ⟨hk⟩
  obtain ⟨j, m, hj, hm, hoverlap, hcollision⟩ :=
    exists_dyadic_seed_counts q.mass b hq hqb B hB n hn
  apply no_identityTest_of_multibin_seeds q (cellWeights q j) (cellLaw q.mass hq j)
    (mixture_cellLaw q hq j) m hm (fun l => dyadicUpper b l.val) ?_ ε n
      (hoverlap.trans_lt hgap) (hcollision.trans_lt hBsample)
  intro l x hx
  have hcell := (cellLaw_positive_iff q.mass hq j l x).mp hx
  have heq : j x = l.val := congrArg Subtype.val hcell
  simpa only [heq] using hj x

end IdentityTesting.EmpiricalSeeds
