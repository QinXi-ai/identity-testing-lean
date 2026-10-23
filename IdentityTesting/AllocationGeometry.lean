import IdentityTesting.AllocationStationarity

/-!
# Mass monotonicity of actual optimal allocation coordinates

The scalar KKT shape `x^3 / (1-x^4)^2` increases on `(0,1)`.  The positive
quotient `(1-x^4)/x = 1/x-x^3` decreases there, so its square gives the
opposite displacement order.  The final optimizer theorem constructs its KKT
scalar from global maximality; stationarity is not a caller premise.
-/

namespace IdentityTesting

open scoped BigOperators

noncomputable def allocationKktShape (x : ℝ) : ℝ :=
  x ^ 3 / (1 - x ^ 4) ^ 2

theorem allocationKktShape_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < allocationKktShape x := by
  have hden : 0 < 1 - x ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  unfold allocationKktShape
  positivity

/-- The scalar KKT shape is strictly increasing on its actual coordinate
domain. -/
theorem allocationKktShape_lt {x y : ℝ}
    (hx0 : 0 < x) (hxy : x < y) (hy1 : y < 1) :
    allocationKktShape x < allocationKktShape y := by
  have hy0 : 0 < y := hx0.trans hxy
  have hx1 : x < 1 := hxy.trans hy1
  have hdx : 0 < 1 - x ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  have hdy : 0 < 1 - y ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hy0.le hy1)
  have hp4 : x ^ 4 < y ^ 4 := pow_lt_pow_left₀ hxy hx0.le (by norm_num)
  have hdle : (1 - y ^ 4) ^ 2 ≤ (1 - x ^ 4) ^ 2 :=
    pow_le_pow_left₀ hdy.le (by linarith only [hp4]) 2
  have hp3 : x ^ 3 < y ^ 3 := pow_lt_pow_left₀ hxy hx0.le (by norm_num)
  unfold allocationKktShape
  calc
    x ^ 3 / (1 - x ^ 4) ^ 2 < y ^ 3 / (1 - x ^ 4) ^ 2 :=
      (div_lt_div_iff_of_pos_right (pow_pos hdx 2)).2 hp3
    _ ≤ y ^ 3 / (1 - y ^ 4) ^ 2 :=
      div_le_div_of_nonneg_left (pow_nonneg hy0.le 3) (pow_pos hdy 2) hdle

/-- Normalizing a supplied scalar KKT equation.  The actual optimizer theorem
below obtains that equation from feasible variations. -/
theorem allocation_stationarity_shape {a β x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1)
    (hstationary : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) :
    a * allocationKktShape x = β := by
  have hden : 1 - x ^ 4 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1))
  have h := (div_eq_iff (pow_ne_zero 2 hden)).2 hstationary
  simpa only [allocationKktShape, mul_div_assoc] using h

/-- Conditional scalar coordinate order for two KKT equations at the same
multiplier. -/
theorem allocation_stationary_coordinate_order {a b β x y : ℝ}
    (hb : 0 < b) (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hab : a ≤ b)
    (hxstationary : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hystationary : b * y ^ 3 = β * (1 - y ^ 4) ^ 2) :
    y ≤ x := by
  by_contra hnot
  have hxy : x < y := lt_of_not_ge hnot
  have hshape := allocationKktShape_lt hx0 hxy hy1
  have hxshape := allocation_stationarity_shape hx0 hx1 hxstationary
  have hyshape := allocation_stationarity_shape hy0 hy1 hystationary
  have hle := mul_le_mul_of_nonneg_right hab (allocationKktShape_pos hx0 hx1).le
  have hlt := mul_lt_mul_of_pos_left hshape hb
  have hcontra := hle.trans_lt hlt
  rw [hxshape, hyshape] at hcontra
  exact (lt_irrefl β) hcontra

/-- The displacement quotient is exactly the positive decreasing expression
`1/x - x^3` in the manuscript's coordinate range. -/
theorem allocation_displacement_quotient_eq {x : ℝ} (hx0 : 0 < x) :
    (1 - x ^ 4) / x = 1 / x - x ^ 3 := by
  field_simp [ne_of_gt hx0]

theorem allocation_displacement_quotient_nonneg {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) : 0 ≤ (1 - x ^ 4) / x :=
  div_nonneg (sub_nonneg.mpr (allocation_fourth_lt_one hx0.le hx1).le) hx0.le

/-- This algebraic quotient order replaces the derivative sign calculation for
the manuscript's displacement shape. -/
theorem allocation_displacement_quotient_antitone {x y : ℝ}
    (hx0 : 0 < x) (hxy : x ≤ y) (hy1 : y < 1) :
    (1 - y ^ 4) / y ≤ (1 - x ^ 4) / x := by
  have hy0 : 0 < y := hx0.trans_le hxy
  have hx1 : x < 1 := hxy.trans_lt hy1
  have hnum : 1 - y ^ 4 ≤ 1 - x ^ 4 := by
    have h := pow_le_pow_left₀ hx0.le hxy 4
    linarith only [h]
  calc
    (1 - y ^ 4) / y ≤ (1 - x ^ 4) / y :=
      (div_le_div_iff_of_pos_right hy0).2 hnum
    _ ≤ (1 - x ^ 4) / x :=
      div_le_div_of_nonneg_left
        (sub_nonneg.mpr (allocation_fourth_lt_one hx0.le hx1).le) hx0 hxy

/-- Conditional scalar rewriting of the KKT displacement. -/
theorem allocation_stationarity_displacement {a β x : ℝ} (hx0 : 0 < x)
    (hstationary : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) :
    a * x = β * ((1 - x ^ 4) / x) ^ 2 := by
  have hmul : (a * x) * x ^ 2 = β * (1 - x ^ 4) ^ 2 := by
    nlinarith only [hstationary]
  have h := (eq_div_iff (pow_ne_zero 2 (ne_of_gt hx0))).2 hmul
  calc
    a * x = β * (1 - x ^ 4) ^ 2 / x ^ 2 := h
    _ = β * ((1 - x ^ 4) / x) ^ 2 := by rw [div_pow]; ring

/-- The two monotonic geometry conclusions from common scalar KKT equations.
This is a reusable conditional lemma, not the final optimizer construction. -/
theorem allocation_stationary_geometry {a b β x y : ℝ}
    (hb : 0 < b) (hβ : 0 < β)
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) (hab : a ≤ b)
    (hxstationary : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hystationary : b * y ^ 3 = β * (1 - y ^ 4) ^ 2) :
    y ≤ x ∧ a * x ≤ b * y := by
  have horder := allocation_stationary_coordinate_order hb hx0 hx1 hy0 hy1 hab
    hxstationary hystationary
  refine ⟨horder, ?_⟩
  have hquot := allocation_displacement_quotient_antitone hy0 horder hx1
  have hsquare := pow_le_pow_left₀
    (allocation_displacement_quotient_nonneg hx0 hx1) hquot 2
  rw [allocation_stationarity_displacement hx0 hxstationary,
    allocation_stationarity_displacement hy0 hystationary]
  exact mul_le_mul_of_nonneg_left hsquare hβ.le

/-- The manuscript's two geometry orders hold at every actual global
maximizer.  Interiority and the common positive KKT scalar are derived from
global maximality inside this theorem. -/
theorem allocation_maximizer_geometry {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    ∀ i j, a i ≤ a j →
      allocationCoordinate t (a j) (u j) ≤ allocationCoordinate t (a i) (u i) ∧
        a i * allocationCoordinate t (a i) (u i) ≤
          a j * allocationCoordinate t (a j) (u j) := by
  have huPos := allocation_maximizer_pos ht ha hu0 hu1 hmax
  obtain ⟨β, hβ, hstationary⟩ := allocation_maximizer_kkt_exists ht ha huPos hu1 hmax
  intro i j hab
  exact allocation_stationary_geometry (ha j) hβ
    (allocationCoordinate_pos ht (ha i) (huPos i))
    (allocationCoordinate_range ht (ha i) (hu0 i)).2
    (allocationCoordinate_pos ht (ha j) (huPos j))
    (allocationCoordinate_range ht (ha j) (hu0 j)).2 hab
    (hstationary i) (hstationary j)

/-- Geometry with the literal real-power original objective as the maximizing
property.  No stationarity or multiplier hypothesis is passed by the caller. -/
theorem manuscript_allocation_maximizer_geometry
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
        ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) :
    ∀ i j, a i ≤ a j →
      allocationCoordinate t (a j) (u j) ≤ allocationCoordinate t (a i) (u i) ∧
        a i * allocationCoordinate t (a i) (u i) ≤
          a j * allocationCoordinate t (a j) (u j) := by
  refine allocation_maximizer_geometry ht ha hu0 hu1 ?_
  intro v hv0 hv1
  rw [allocationObjective_eq_rpow ht ha hv0, allocationObjective_eq_rpow ht ha hu0]
  exact hmax v hv0 hv1

/-- An actual positive full-budget original optimizer with both geometry
orders exists from the positive masses and time alone. -/
theorem exists_manuscript_allocation_optimizer_geometry
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      (∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ∧
      ∀ i j, a i ≤ a j →
        allocationCoordinate t (a j) (u j) ≤ allocationCoordinate t (a i) (u i) ∧
          a i * allocationCoordinate t (a i) (u i) ≤
            a j * allocationCoordinate t (a j) (u j) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_manuscript_positive_saturated_allocation_maximizer ht ha
  exact ⟨u, hu0, hu1, hmax,
    manuscript_allocation_maximizer_geometry ht ha (fun i => (hu0 i).le) hu1.le hmax⟩

end IdentityTesting
