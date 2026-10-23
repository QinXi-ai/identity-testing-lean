import IdentityTesting.HeavyLowerGeometry
import Mathlib.Data.Finset.Lattice.Fold

/-! Original feasible-allocation geometry in `hh:compression`.
The budget is at most one; no optimizer or full-budget equality is required.
The existing H/S split and Cauchy--Schwarz lemma are reused. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyCompressionFeasible
open FiniteTesting HeavySignedFamily HeavyLowerGeometry

variable {k : ℕ}

theorem quarter_coordinate_ratio {a x : ℝ}
    (hx : (1 : ℝ) / 4 ≤ x) (hx1 : x < 1) :
    a ^ 2 / (1 - x) ≤ 1024 * (a ^ 2 * x ^ 4 / (1 - x ^ 4)) := by
  have hx0 : 0 ≤ x := by linarith
  have hx4 : x ^ 4 < 1 := allocation_fourth_lt_one hx0 hx1
  have hx4lower : (1 : ℝ) / 256 ≤ x ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hx 4
    norm_num at h
    exact h
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx1.le)]
  have hx3 : x ^ 3 ≤ 1 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1.le), hx2]
  have hshape : 1 + x + x ^ 2 + x ^ 3 ≤ 1024 * x ^ 4 := by
    linarith only [hx1.le, hx2, hx3, hx4lower]
  have hfactor : 1 - x ^ 4 = (1 - x) * (1 + x + x ^ 2 + x ^ 3) := by ring
  have hscaled := mul_le_mul_of_nonneg_left hshape (sub_nonneg.mpr hx1.le)
  rw [← hfactor] at hscaled
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sub_pos.mpr hx1) (sub_pos.mpr hx4)).2
  nlinarith only [mul_le_mul_of_nonneg_left hscaled (sq_nonneg a)]

theorem quarter_subset_moment_bound {ι : Type*} [Fintype ι]
    (s : Finset ι) (a x : ι → ℝ) {T : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hhigh : ∀ i ∈ s, (1 : ℝ) / 4 ≤ x i)
    (hbudget : T ^ 2 * (∑ i, a i ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤ 1) :
    T ^ 2 * (∑ i ∈ s, a i ^ ((3 : ℝ) / 2)) ^ 2 ≤
      1024 * ∑ i ∈ s, a i * (1 - x i) := by
  have hcost : ∀ i, 0 ≤ a i ^ 2 * x i ^ 4 / (1 - x i ^ 4) := by
    intro i
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2).le)
  have hsubset : (∑ i ∈ s, a i ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤
      ∑ i, a i ^ 2 * x i ^ 4 / (1 - x i ^ 4) :=
    Finset.sum_le_univ_sum_of_nonneg hcost
  have hrat : (∑ i ∈ s, a i ^ 2 / (1 - x i)) ≤
      1024 * ∑ i, a i ^ 2 * x i ^ 4 / (1 - x i ^ 4) := by
    calc
      _ ≤ ∑ i ∈ s, 1024 * (a i ^ 2 * x i ^ 4 / (1 - x i ^ 4)) :=
        Finset.sum_le_sum (fun i hi => quarter_coordinate_ratio (hhigh i hi) (hx i).2)
      _ = 1024 * ∑ i ∈ s, a i ^ 2 * x i ^ 4 / (1 - x i ^ 4) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsubset (by norm_num)
  have hratT : T ^ 2 * (∑ i ∈ s, a i ^ 2 / (1 - x i)) ≤ 1024 := by
    have h := mul_le_mul_of_nonneg_left hrat (sq_nonneg T)
    nlinarith only [h, hbudget]
  have hE : 0 ≤ ∑ i ∈ s, a i * (1 - x i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sub_nonneg.mpr (hx i).2.le))
  calc
    _ ≤ T ^ 2 * ((∑ i ∈ s, a i ^ 2 / (1 - x i)) * ∑ i ∈ s, a i * (1 - x i)) :=
      mul_le_mul_of_nonneg_left (allocation_subset_cauchy s a x
        (fun i _ => ha i) (fun i _ => (hx i).2)) (sq_nonneg T)
    _ = (T ^ 2 * ∑ i ∈ s, a i ^ 2 / (1 - x i)) * ∑ i ∈ s, a i * (1 - x i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratT hE

theorem high_moment_bound (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ}
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤ 1) :
    T ^ 2 * (∑ i ∈ highTail x, q.mass i.succ ^ ((3 : ℝ) / 2)) ^ 2 ≤
      1024 * highSlack q x :=
  quarter_subset_moment_bound (highTail x) (fun i => q.mass i.succ) x
    (fun i => q.nonneg _) hx (fun i hi => ((mem_highTail x i).mp hi).le) hbudget

theorem tail_coordinate_bound (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ}
    (hbudget : T ^ 2 * (∑ j, q.mass j.succ ^ 2 * x j ^ 4 / (1 - x j ^ 4)) ≤ 1)
    (i : Fin k) : T * q.mass i.succ * x i ^ 2 ≤ 1 := by
  have hcost : ∀ j, 0 ≤ q.mass j.succ ^ 2 * x j ^ 4 / (1 - x j ^ 4) := by
    intro j
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx j).1 (hx j).2).le)
  have hraw : q.mass i.succ ^ 2 * x i ^ 4 ≤
      q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4) := by
    apply (le_div_iff₀ (sub_pos.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2))).2
    nlinarith only [mul_nonneg (sq_nonneg (q.mass i.succ)) (sq_nonneg (x i ^ 4))]
  have hsingle := Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have hrawT := mul_le_mul_of_nonneg_left (hraw.trans hsingle) (sq_nonneg T)
  have hb := hrawT.trans hbudget
  nlinarith only [hb, sq_nonneg (T * q.mass i.succ * x i ^ 2 - 1)]

theorem high_atom_lt (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ j, q.mass j.succ ^ 2 * x j ^ 4 / (1 - x j ^ 4)) ≤ 1)
    (i : Fin k) (hi : i ∈ highTail x) : q.mass i.succ < 16 / T := by
  apply (lt_div_iff₀ hT).2
  have hxi := (mem_highTail x i).mp hi
  have hsq : (1 : ℝ) / 16 < x i ^ 2 := by
    have h := mul_pos (sub_pos.mpr hxi) (show 0 < x i + 1 / 4 by linarith only [hxi])
    nlinarith only [h]
  have hm := mul_lt_mul_of_pos_left hsq (mul_pos hT (hq i.succ))
  have hc := tail_coordinate_bound q x hx hbudget i
  nlinarith only [hm, hc]

/-- The actual maximum on S, with the manuscript's empty-set convention. -/
def highAtomMax (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) : ℝ :=
  if h : (highTail x).Nonempty then (highTail x).sup' h (fun i => q.mass i.succ) else 0

theorem highAtomMax_empty (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (h : highTail x = ∅) : highAtomMax q x = 0 := by simp [highAtomMax, h]

theorem high_atom_le_max (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (i : Fin k) (hi : i ∈ highTail x) : q.mass i.succ ≤ highAtomMax q x := by
  rw [highAtomMax, dif_pos ⟨i, hi⟩]
  exact Finset.le_sup' (fun j => q.mass j.succ) hi

theorem highAtomMax_nonneg (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) :
    0 ≤ highAtomMax q x := by
  by_cases h : (highTail x).Nonempty
  · obtain ⟨i, hi⟩ := h
    exact (q.nonneg i.succ).trans (high_atom_le_max q x i hi)
  · simp [highAtomMax, h]

theorem highAtomMax_lt (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ j, q.mass j.succ ^ 2 * x j ^ 4 / (1 - x j ^ 4)) ≤ 1) :
    highAtomMax q x < 16 / T := by
  by_cases h : (highTail x).Nonempty
  · rw [highAtomMax, dif_pos h, Finset.sup'_lt_iff]
    exact fun i hi => high_atom_lt q x hq hx hT hbudget i hi
  · simp only [highAtomMax, dif_neg h]
    positivity

theorem seed_atom_le_max (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (i : Fin (k + 1)) (hi : i ∈ seedSet x) : q.mass i ≤ highAtomMax q x := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  exact high_atom_le_max q x j hj

/-- The original geometry portion of `hh:compression`, including both exact
constants, feasible budget, and the empty subset. -/
theorem compression_geometry (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤ 1) :
    (∑ i, q.mass i.succ * x i) = lowDisplacement q x + highMass q x - highSlack q x ∧
    T ^ 2 * (∑ i ∈ highTail x, q.mass i.succ ^ ((3 : ℝ) / 2)) ^ 2 ≤ 1024 * highSlack q x ∧
    highAtomMax q x < 16 / T := by
  refine ⟨?_, high_moment_bound q x hx hbudget, highAtomMax_lt q x hq hx hT hbudget⟩
  simpa using radius_identity q x (g := 0) (ε := ∑ i, q.mass i.succ * x i) (by ring)

end IdentityTesting.HeavyCompressionFeasible
