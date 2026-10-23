import IdentityTesting.AllocationFiniteBridge
import IdentityTesting.PairedPerturbation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Scalar rate estimates at the original allocation root

The high-coordinate estimate is valid on any subset on which `1/8 ≤ x`.
The paired estimate charges injectively selected right endpoints against the
same exact transformed budget.  Final callers construct the coordinates from
the original allocation root rather than accepting a budget certificate.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting

theorem allocation_high_coordinate_ratio {q x : ℝ}
    (hx : (1 : ℝ) / 8 ≤ x) (hx1 : x < 1) :
    q ^ 2 / (1 - x) ≤ 16384 * (q ^ 2 * x ^ 4 / (1 - x ^ 4)) := by
  have hx0 : 0 ≤ x := by linarith
  have hx4 : x ^ 4 < 1 := allocation_fourth_lt_one hx0 hx1
  have hx4lower : (1 : ℝ) / 4096 ≤ x ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) hx 4
    norm_num at h
    exact h
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg hx0 (sub_nonneg.mpr hx1.le)]
  have hx3 : x ^ 3 ≤ 1 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1.le), hx2]
  have hshape : 1 + x + x ^ 2 + x ^ 3 ≤ 16384 * x ^ 4 := by
    linarith only [hx1.le, hx2, hx3, hx4lower]
  have hfactor : 1 - x ^ 4 = (1 - x) * (1 + x + x ^ 2 + x ^ 3) := by ring
  have hscaled := mul_le_mul_of_nonneg_left hshape (sub_nonneg.mpr hx1.le)
  rw [← hfactor] at hscaled
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sub_pos.mpr hx1) (sub_pos.mpr hx4)).2
  nlinarith only [mul_le_mul_of_nonneg_left hscaled (sq_nonneg q)]

theorem allocation_three_halves_eq {q : ℝ} (hq : 0 ≤ q) :
    q ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hq (by norm_num) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem allocation_subset_cauchy {ι : Type*} (s : Finset ι) (q x : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hx1 : ∀ i ∈ s, x i < 1) :
    (∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)) ^ 2 ≤
      (∑ i ∈ s, (q i) ^ 2 / (1 - x i)) *
        ∑ i ∈ s, q i * (1 - x i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun i => q i * Real.sqrt (q i))
    (f := fun i => (q i) ^ 2 / (1 - x i))
    (g := fun i => q i * (1 - x i))
    (fun i hi => div_nonneg (sq_nonneg _) (sub_nonneg.mpr (hx1 i hi).le))
    (fun i hi => mul_nonneg (hq i hi) (sub_nonneg.mpr (hx1 i hi).le)) ?_
  · have heq : (∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)) =
        ∑ i ∈ s, q i * Real.sqrt (q i) :=
      Finset.sum_congr rfl (fun i hi => allocation_three_halves_eq (hq i hi))
    rw [heq]
    exact h
  · intro i hi
    rw [mul_pow, Real.sq_sqrt (hq i hi)]
    field_simp [ne_of_gt (sub_pos.mpr (hx1 i hi))]

theorem allocation_high_subset_bound {ι : Type*} [Fintype ι]
    (s : Finset ι) (q x : ι → ℝ) {T : ℝ}
    (hq : ∀ i, 0 ≤ q i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hhigh : ∀ i ∈ s, (1 : ℝ) / 8 ≤ x i)
    (hbudget : T ^ 2 * (∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    T ^ 2 * (∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)) ^ 2 ≤
      16384 * ∑ i ∈ s, q i * (1 - x i) := by
  have hcost : ∀ i, 0 ≤ (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    intro i
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2).le)
  have hsubset : (∑ i ∈ s, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤
      ∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => hcost i)
  have hrat : (∑ i ∈ s, (q i) ^ 2 / (1 - x i)) ≤
      16384 * ∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    calc
      _ ≤ ∑ i ∈ s, 16384 * ((q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) :=
        Finset.sum_le_sum (fun i hi => allocation_high_coordinate_ratio (hhigh i hi) (hx i).2)
      _ = 16384 * ∑ i ∈ s, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsubset (by norm_num)
  have hratT : T ^ 2 * (∑ i ∈ s, (q i) ^ 2 / (1 - x i)) ≤ 16384 := by
    calc
      _ ≤ T ^ 2 * (16384 * ∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) :=
        mul_le_mul_of_nonneg_left hrat (sq_nonneg T)
      _ = 16384 := by nlinarith only [hbudget]
  have hE : 0 ≤ ∑ i ∈ s, q i * (1 - x i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (sub_nonneg.mpr (hx i).2.le))
  calc
    _ ≤ T ^ 2 * ((∑ i ∈ s, (q i) ^ 2 / (1 - x i)) *
        ∑ i ∈ s, q i * (1 - x i)) :=
      mul_le_mul_of_nonneg_left (allocation_subset_cauchy s q x
        (fun i _ => hq i) (fun i _ => (hx i).2)) (sq_nonneg T)
    _ = (T ^ 2 * ∑ i ∈ s, (q i) ^ 2 / (1 - x i)) *
        ∑ i ∈ s, q i * (1 - x i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hratT hE

theorem allocation_paired_coefficient_scalar {l r x : ℝ}
    (hr : 0 < r) (hrl : r ≤ l) (hx : 0 ≤ x ∧ x < 1) :
    ((8 * r * x) ^ 2 * (1 / l + 1 / r)) ^ 2 ≤
      16384 * (r ^ 2 * x ^ 4 / (1 - x ^ 4)) := by
  have hl : 0 < l := lt_of_lt_of_le hr hrl
  have hinv : 1 / l ≤ 1 / r := one_div_le_one_div_of_le hr hrl
  have hM0 : 0 ≤ (8 * r * x) ^ 2 * (1 / l + 1 / r) := by positivity
  have hM : (8 * r * x) ^ 2 * (1 / l + 1 / r) ≤ 128 * r * x ^ 2 := by
    calc
      _ ≤ (8 * r * x) ^ 2 * (2 / r) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        calc
          1 / l + 1 / r ≤ 1 / r + 1 / r := add_le_add_right hinv _
          _ = 2 / r := by ring
      _ = _ := by field_simp [ne_of_gt hr]; ring
  have hsq := pow_le_pow_left₀ hM0 hM 2
  have hx4 : x ^ 4 < 1 := allocation_fourth_lt_one hx.1 hx.2
  have hcost : r ^ 2 * x ^ 4 ≤ r ^ 2 * x ^ 4 / (1 - x ^ 4) := by
    apply (le_div_iff₀ (sub_pos.mpr hx4)).2
    nlinarith only [mul_nonneg (sq_nonneg r) (sq_nonneg (x ^ 4))]
  calc
    _ ≤ (128 * r * x ^ 2) ^ 2 := hsq
    _ = 16384 * (r ^ 2 * x ^ 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by norm_num)

theorem allocation_paired_coefficient_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (q x : ι → ℝ) (L R : κ → ι) (hR : Function.Injective R)
    {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q i)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (horder : ∀ j, q (R j) ≤ q (L j))
    (hbudget : T ^ 2 * (∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    (∑ j, ((8 * q (R j) * x (R j)) ^ 2 *
      (1 / q (L j) + 1 / q (R j))) ^ 2) ≤ 16384 / T ^ 2 := by
  have hcost : ∀ i, 0 ≤ (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    intro i
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2).le)
  have hcharge : (∑ j, (q (R j)) ^ 2 * (x (R j)) ^ 4 / (1 - (x (R j)) ^ 4)) ≤
      ∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    calc
      _ = ∑ i ∈ Finset.univ.image R, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
        rw [Finset.sum_image]
        exact fun a _ b _ hab => hR hab
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hcost
  have hsum : (∑ j, ((8 * q (R j) * x (R j)) ^ 2 *
      (1 / q (L j) + 1 / q (R j))) ^ 2) ≤
      16384 * ∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    calc
      _ ≤ ∑ j, 16384 * ((q (R j)) ^ 2 * (x (R j)) ^ 4 /
          (1 - (x (R j)) ^ 4)) :=
        Finset.sum_le_sum (fun j _ => allocation_paired_coefficient_scalar
          (hq (R j)) (horder j) (hx (R j)))
      _ = 16384 * ∑ j, (q (R j)) ^ 2 * (x (R j)) ^ 4 / (1 - (x (R j)) ^ 4) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcharge (by norm_num)
  apply (le_div_iff₀ (sq_pos_of_pos hT)).2
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg T)
  nlinarith only [hscaled, hbudget]

theorem pairedCoefficient_allocation_bound {d u : ℕ}
    (q : FiniteTesting.Probability (Fin (d + (d + u)))) (x : Fin (d + (d + u)) → ℝ)
    {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q.mass i)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (horder : ∀ j, q.mass (PairedPerturbation.rightIndex j) ≤
      q.mass (PairedPerturbation.leftIndex j))
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    (∑ j, (PairedPerturbation.pairedCoefficient q
      (fun j => 8 * q.mass (PairedPerturbation.rightIndex j) *
        x (PairedPerturbation.rightIndex j)) j) ^ 2) ≤ 16384 / T ^ 2 := by
  apply allocation_paired_coefficient_bound q.mass x PairedPerturbation.leftIndex
    PairedPerturbation.rightIndex ?_ hT hq hx horder hbudget
  intro a b hab
  apply Fin.ext
  have hh := congrArg Fin.val hab
  change d + a.val = d + b.val at hh
  exact Nat.add_left_cancel hh

/-- Both manuscript scalar estimates hold for coordinates constructed at the
original root. The high-coordinate subset may include the boundary `x = 1/8`. -/
theorem exists_original_root_coordinates_with_rate_bounds {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot (extendFiniteLaw q) e ∧
      ∃ x : Fin k → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i * x i) = e ∧
        (allocationRoot (extendFiniteLaw q) e) ^ 2 *
          (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1 ∧
        (∀ s : Finset (Fin k), (∀ i ∈ s, (1 : ℝ) / 8 ≤ x i) →
          (allocationRoot (extendFiniteLaw q) e) ^ 2 *
            (∑ i ∈ s, (q.mass i) ^ ((3 : ℝ) / 2)) ^ 2 ≤
              16384 * ∑ i ∈ s, q.mass i * (1 - x i)) ∧
        (∀ (κ : Type) [Fintype κ] (L R : κ → Fin k), Function.Injective R →
          (∀ j, q.mass (R j) ≤ q.mass (L j)) →
          (∑ j, ((8 * q.mass (R j) * x (R j)) ^ 2 *
            (1 / q.mass (L j) + 1 / q.mass (R j))) ^ 2) ≤
              16384 / (allocationRoot (extendFiniteLaw q) e) ^ 2) := by
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, hfinal⟩ :=
    exists_finite_allocation_coordinates_at_root q hq he0 he1
  refine ⟨hT, x, hx, hsum, hbudget, ?_, ?_⟩
  · intro s hs
    exact allocation_high_subset_bound s q.mass x (fun i => (hq i).le)
      (fun i => ⟨(hx i).1.le, (hx i).2⟩) hs hbudget
  · intro κ _ L R hR horder
    exact allocation_paired_coefficient_bound q.mass x L R hR hT hq
      (fun i => ⟨(hx i).1.le, (hx i).2⟩) horder hbudget

/-- The concrete paired construction receives both rate estimates at the
original root; its coefficient is the one used by the actual signed prior. -/
theorem exists_paired_original_root_coordinates_with_rate_bounds {d u : ℕ}
    (q : FiniteTesting.Probability (Fin (d + (d + u)))) (hq : ∀ i, 0 < q.mass i)
    (horder : ∀ j, q.mass (PairedPerturbation.rightIndex j) ≤
      q.mass (PairedPerturbation.leftIndex j))
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot (extendFiniteLaw q) e ∧
      ∃ x : Fin (d + (d + u)) → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i * x i) = e ∧
        (allocationRoot (extendFiniteLaw q) e) ^ 2 *
          (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1 ∧
        (allocationRoot (extendFiniteLaw q) e) ^ 2 *
          (∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / 8 < x i),
            (q.mass i) ^ ((3 : ℝ) / 2)) ^ 2 ≤
              16384 * ∑ i ∈ Finset.univ.filter (fun i => (1 : ℝ) / 8 < x i),
                q.mass i * (1 - x i) ∧
        (∑ j, (PairedPerturbation.pairedCoefficient q
          (fun j => 8 * q.mass (PairedPerturbation.rightIndex j) *
            x (PairedPerturbation.rightIndex j)) j) ^ 2) ≤
              16384 / (allocationRoot (extendFiniteLaw q) e) ^ 2 := by
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, hfinal⟩ :=
    exists_finite_allocation_coordinates_at_root q hq he0 he1
  refine ⟨hT, x, hx, hsum, hbudget, ?_, ?_⟩
  · apply allocation_high_subset_bound _ q.mass x (fun i => (hq i).le)
      (fun i => ⟨(hx i).1.le, (hx i).2⟩) _ hbudget
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  · exact pairedCoefficient_allocation_bound q x hT hq
      (fun i => ⟨(hx i).1.le, (hx i).2⟩) horder hbudget

end IdentityTesting
