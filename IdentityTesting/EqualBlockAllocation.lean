import IdentityTesting.AllocationScaling
import IdentityTesting.AllocationFiniteBridge
import IdentityTesting.AllocationGeometry

/-! Exact allocation of a block of equal positive masses.
The block size is positive, and a zero budget is treated separately. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

/-- An actual optimizer with identical masses allocates `1/k` to each atom. -/
theorem equal_mass_maximizer_coordinates {k : ℕ} (hk : 0 < k)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {u : Fin k → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ w : Fin k → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      allocationObjective t (fun _ => a) w ≤ allocationObjective t (fun _ => a) u) :
    ∀ i, u i = 1 / (k : ℝ) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hgeom := allocation_maximizer_geometry ht (fun _ => ha) hu0 hu1 hmax
  have heq : ∀ i j, u i = u j := by
    intro i j
    have hx := le_antisymm (hgeom j i le_rfl).1 (hgeom i j le_rfl).1
    rw [← allocationCost_coordinate ht ha (hu0 i),
      ← allocationCost_coordinate ht ha (hu0 j), hx]
  have hsum := allocation_maximizer_saturated ht (fun _ => ha) hu0 hu1 hmax
  intro i
  have hsum' : (k : ℝ) * u i = 1 := by
    calc
      (k : ℝ) * u i = ∑ _j : Fin k, u i := by simp
      _ = ∑ j, u j := Finset.sum_congr rfl (fun j _ => (heq j i).symm)
      _ = 1 := hsum
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))).mpr
  simpa [mul_comm] using hsum'

/-- Equal division is a global optimizer, obtained from optimizer existence
and the proved equal-coordinate property. -/
theorem equal_mass_allocation_maximum {k : ℕ} (hk : 0 < k)
    {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (u : Fin k → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1) :
    allocationObjective t (fun _ => a) u ≤
      allocationObjective t (fun _ : Fin k => a) (fun _ => 1 / (k : ℝ)) := by
  obtain ⟨w, hw0, hw1, hmax⟩ := exists_allocation_maximizer ht (fun _ : Fin k => ha)
  have heq := equal_mass_maximizer_coordinates hk ht ha hw0 hw1 hmax
  have hw : w = fun _ => 1 / (k : ℝ) := funext heq
  simpa [hw] using hmax u hu0 hu1

theorem equal_block_unit_objective {k : ℕ} (hk : 0 < k)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    allocationObjective t (fun _ : Fin k => r / (k : ℝ))
      (fun _ => 1 / (k : ℝ)) = r * (1 + t ^ 2 * r ^ 2 / k) ^ (-1 / 4 : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [allocationObjective_eq_rpow ht (fun _ => div_pos hr hkpos)
    (fun _ => (div_pos zero_lt_one hkpos).le)]
  have hratio : (1 / (k : ℝ)) / (1 / k + t ^ 2 * (r / k) ^ 2) =
      (1 + t ^ 2 * r ^ 2 / k)⁻¹ := by
    field_simp
  simp only [hratio, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Real.inv_rpow (by positivity : 0 ≤ 1 + t ^ 2 * r ^ 2 / k)]
  rw [← Real.rpow_neg (by positivity : 0 ≤ 1 + t ^ 2 * r ^ 2 / k)]
  field_simp

/-- The equal block formula is the original countable `allocationD`, with the
finite block extended by zeros; it is not a newly defined surrogate. -/
theorem allocationD_equal_block {k : ℕ} (hk : 0 < k)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    allocationD (extendFiniteVector (fun _ : Fin k => r / (k : ℝ))) t =
      r * (1 + t ^ 2 * r ^ 2 / k) ^ (-1 / 4 : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [allocationD_extendFiniteVector_eq_optimizer ht (fun _ => div_pos hr hkpos)
    (u := fun _ => 1 / (k : ℝ))]
  · exact equal_block_unit_objective hk ht hr
  · constructor
    · intro i; positivity
    · simp [ne_of_gt hkpos]
  · exact fun u hu0 hu1 => equal_mass_allocation_maximum hk ht
      (div_pos hr hkpos) u hu0 hu1

/-- Rescale a positive block budget to the unit simplex. -/
theorem allocationObjective_budget_scale {ι : Type*} [Fintype ι]
    (t : ℝ) (a u : ι → ℝ) {v : ℝ} (hv : 0 < v) :
    allocationObjective t a u =
      allocationObjective (t / Real.sqrt v) a (fun i => u i / v) := by
  unfold allocationObjective allocationCoordinate
  apply Finset.sum_congr rfl
  intro i hi
  rw [div_pow, Real.sq_sqrt hv.le]
  have hden : u i / v + t ^ 2 / v * a i ^ 2 = (u i + t ^ 2 * a i ^ 2) / v := by ring
  rw [hden, div_div_div_cancel_right₀ (ne_of_gt hv)]

theorem equal_block_positive_budget_objective {k : ℕ} (hk : 0 < k)
    {t r v : ℝ} (ht : 0 < t) (hr : 0 < r) (hv : 0 < v) :
    allocationObjective t (fun _ : Fin k => r / (k : ℝ)) (fun _ => v / (k : ℝ)) =
      r * (1 + t ^ 2 * r ^ 2 / ((k : ℝ) * v)) ^ (-1 / 4 : ℝ) := by
  rw [allocationObjective_budget_scale t _ _ hv]
  have hquot : (fun _ : Fin k => v / (k : ℝ) / v) = fun _ => 1 / (k : ℝ) := by
    funext i
    field_simp
  rw [hquot, equal_block_unit_objective hk (div_pos ht (Real.sqrt_pos.2 hv)) hr,
    div_pow, Real.sq_sqrt hv.le]
  congr 2
  ring

/-- For any positive block budget, equal division maximizes the original
objective among all nonnegative allocations using at most that budget. -/
theorem equal_block_positive_budget_bound {k : ℕ} (hk : 0 < k)
    {t r v : ℝ} (ht : 0 < t) (hr : 0 < r) (hv : 0 < v)
    (u : Fin k → ℝ) (hu0 : ∀ i, 0 ≤ u i) (huv : (∑ i, u i) ≤ v) :
    allocationObjective t (fun _ => r / (k : ℝ)) u ≤
      r * (1 + t ^ 2 * r ^ 2 / ((k : ℝ) * v)) ^ (-1 / 4 : ℝ) := by
  rw [allocationObjective_budget_scale t _ _ hv]
  have hbudget : (∑ i, u i / v) ≤ 1 := by
    rw [← Finset.sum_div]
    exact (div_le_one hv).2 huv
  have h := equal_mass_allocation_maximum hk (div_pos ht (Real.sqrt_pos.2 hv))
    (div_pos hr (Nat.cast_pos.mpr hk)) (fun i => u i / v)
    (fun i => div_nonneg (hu0 i) hv.le) hbudget
  refine h.trans_eq ?_
  rw [equal_block_unit_objective hk (div_pos ht (Real.sqrt_pos.2 hv)) hr,
    div_pow, Real.sq_sqrt hv.le]
  congr 2
  ring

theorem allocationObjective_zero_budget {ι : Type*} [Fintype ι]
    (t : ℝ) (a u : ι → ℝ) (hu0 : ∀ i, 0 ≤ u i) (huv : (∑ i, u i) ≤ 0) :
    allocationObjective t a u = 0 := by
  have hu : ∀ i, u i = 0 := by
    intro i
    apply le_antisymm _ (hu0 i)
    exact (Finset.single_le_sum (fun j _ => hu0 j) (Finset.mem_univ i)).trans huv
  simp [allocationObjective, allocationCoordinate, hu]

/-- The exact maximum in the equal-block paragraph after `lem:allocation`.
The zero budget case is included explicitly, and the maximizing allocation
is an actual feasible vector, not a supplied optimizer certificate. -/
theorem equal_block_budget_isGreatest {k : ℕ} (hk : 0 < k)
    {t r v : ℝ} (ht : 0 < t) (hr : 0 < r) (hv : 0 ≤ v) :
    IsGreatest {d : ℝ | ∃ u : Fin k → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ v ∧
      d = allocationObjective t (fun _ => r / (k : ℝ)) u}
      (if v = 0 then 0 else r * (1 + t ^ 2 * r ^ 2 / ((k : ℝ) * v)) ^ (-1 / 4 : ℝ)) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  by_cases hv0 : v = 0
  · subst v
    simp only [if_pos rfl]
    constructor
    · refine ⟨fun _ => 0, fun _ => le_rfl, by simp, ?_⟩
      simp [allocationObjective, allocationCoordinate]
    · rintro d ⟨u, hu0, huv, rfl⟩
      exact (allocationObjective_zero_budget t _ u hu0 huv).le
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    rw [if_neg hv0]
    constructor
    · refine ⟨fun _ => v / (k : ℝ), fun _ => div_nonneg hv hkpos.le, ?_, ?_⟩
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact le_of_eq (by field_simp)
      · exact (equal_block_positive_budget_objective hk ht hr hvpos).symm
    · rintro d ⟨u, hu0, huv, rfl⟩
      exact equal_block_positive_budget_bound hk ht hr hvpos u hu0 huv

/-- Equal masses in an arbitrary positive mass vector receive equal allocations
at every actual global optimizer, even when other masses are different. -/
theorem allocation_maximizer_equal_masses {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      allocationObjective t a w ≤ allocationObjective t a u)
    {i j : ι} (hij : a i = a j) : u i = u j := by
  have hgeom := allocation_maximizer_geometry ht ha hu0 hu1 hmax
  have hx := le_antisymm (hgeom j i hij.ge).1 (hgeom i j hij.le).1
  rw [← allocationCost_coordinate ht (ha i) (hu0 i),
    ← allocationCost_coordinate ht (ha j) (hu0 j), hx, hij]

/-- The contribution of an equal-mass block inside a larger, arbitrary actual
optimizer is the same exact budget formula. Other masses may be unequal.
The scalar budget is the sum of the actual allocations on the selected block. -/
theorem allocation_maximizer_equal_block_contribution
    {ι : Type*} [Fintype ι] [Nonempty ι] {k : ℕ} (hk : 0 < k)
    {t r v : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      allocationObjective t a w ≤ allocationObjective t a u)
    (f : Fin k → ι) (hblock : ∀ j, a (f j) = r / (k : ℝ))
    (hbudget : (∑ j, u (f j)) = v) :
    0 < v ∧ (∑ j, a (f j) *
      (u (f j) / (u (f j) + t ^ 2 * a (f j) ^ 2)) ^ (1 / 4 : ℝ)) =
      r * (1 + t ^ 2 * r ^ 2 / ((k : ℝ) * v)) ^ (-1 / 4 : ℝ) := by
  let j0 : Fin k := ⟨0, hk⟩
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hr : 0 < r := by
    have h := ha (f j0)
    rw [hblock j0] at h
    exact (div_pos_iff_of_pos_right hkpos).1 h
  have huPos := allocation_maximizer_pos ht ha hu0 hu1 hmax
  have heq : ∀ j l, u (f j) = u (f l) := by
    intro j l
    exact allocation_maximizer_equal_masses ht ha hu0 hu1 hmax
      ((hblock j).trans (hblock l).symm)
  have hconst : ∀ j, (k : ℝ) * u (f j) = v := by
    intro j
    calc
      (k : ℝ) * u (f j) = ∑ _l : Fin k, u (f j) := by simp
      _ = ∑ l, u (f l) := Finset.sum_congr rfl (fun l _ => (heq l j).symm)
      _ = v := hbudget
  have hv : 0 < v := by rw [← hconst j0]; exact mul_pos hkpos (huPos _)
  have hcoords : ∀ j, u (f j) = v / (k : ℝ) := by
    intro j
    apply (eq_div_iff (ne_of_gt hkpos)).2
    simpa [mul_comm] using hconst j
  refine ⟨hv, ?_⟩
  have hvalue := equal_block_positive_budget_objective hk ht hr hv
  rw [allocationObjective_eq_rpow ht (fun _ => div_pos hr hkpos)
    (fun _ => (div_pos hv hkpos).le)] at hvalue
  simpa only [hblock, hcoords] using hvalue

end IdentityTesting
