import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Algebra of the allocation change of variables

The manuscript's coordinate relation is `x^4 = u / (u + t^2 * a^2)`.
This file proves that its inverse is the nonnegative budget cost
`t^2 * a^2 * x^4 / (1 - x^4)`.  It also proves the finite-sum budget
identity obtained from the manuscript's stationarity equations.

These results establish the algebraic change of variables and its use in
the budget.  They make no assertion about existence or uniqueness of an
optimizer, differentiability, or the existence of a Lagrange multiplier.
-/

namespace IdentityTesting

open scoped BigOperators

/-- The budget charged by a transformed allocation coordinate. -/
noncomputable def allocationCost (t a x : ℝ) : ℝ :=
  t ^ 2 * a ^ 2 * x ^ 4 / (1 - x ^ 4)

/-- The nonnegative fourth root in the manuscript, represented by two square
roots so that its defining fourth-power identity is explicit. -/
noncomputable def allocationCoordinate (t a u : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (u / (u + t ^ 2 * a ^ 2)))

/-- A nonnegative coordinate below one has its fourth power below one. -/
theorem allocation_fourth_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ^ 4 < 1 := by
  have hp : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hx1) (by linarith)
  have hx2 : x ^ 2 < 1 := by nlinarith only [hp]
  have hp2 : 0 < (1 - x ^ 2) * (1 + x ^ 2) :=
    mul_pos (sub_pos.mpr hx2) (by positivity)
  nlinarith only [hp2]

/-- The generic rational inverse, before choosing the fourth-power coordinate. -/
theorem allocation_rational_inverse_iff {u c y : ℝ}
    (hc : 0 < c) (hu : 0 ≤ u) (hy : y < 1) :
    u = c * y / (1 - y) ↔ u / (u + c) = y := by
  have hden : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hsum : u + c ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hu hc)
  constructor
  · intro h
    apply (div_eq_iff hsum).2
    have hmul : u * (1 - y) = c * y := (eq_div_iff hden).1 h
    nlinarith only [hmul]
  · intro h
    apply (eq_div_iff hden).2
    have hmul : u = y * (u + c) := (div_eq_iff hsum).1 h
    nlinarith only [hmul]

/-- Nonnegative allocations give ratios in the interval `[0, 1)`. -/
theorem allocation_ratio_range {u c : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    0 ≤ u / (u + c) ∧ u / (u + c) < 1 := by
  have hsum : 0 < u + c := add_pos_of_nonneg_of_pos hu hc
  constructor
  · exact div_nonneg hu (le_of_lt hsum)
  · apply (div_lt_one hsum).2
    linarith

/-- The inverse coordinate formula is a valid nonnegative allocation. -/
theorem allocationCost_nonneg {t a x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ allocationCost t a x := by
  unfold allocationCost
  apply div_nonneg
  · positivity
  · exact le_of_lt (sub_pos.mpr (allocation_fourth_lt_one hx0 hx1))

/-- The actual manuscript constants instantiate the rational inverse. -/
theorem allocation_inverse_iff {t a u x : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    u = allocationCost t a x ↔ u / (u + t ^ 2 * a ^ 2) = x ^ 4 := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  simpa only [allocationCost, mul_assoc] using
    (allocation_rational_inverse_iff hc hu (allocation_fourth_lt_one hx0 hx1))

/-- Applying the ratio to a cost returns the given fourth-power coordinate. -/
theorem allocationCost_ratio {t a x : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    allocationCost t a x / (allocationCost t a x + t ^ 2 * a ^ 2) = x ^ 4 := by
  exact (allocation_inverse_iff ht ha (allocationCost_nonneg hx0 hx1) hx0 hx1).1 rfl

/-- Conversely, the fourth-power relation reconstructs the original allocation. -/
theorem allocationCost_of_ratio {t a u x : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hcoordinate : u / (u + t ^ 2 * a ^ 2) = x ^ 4) :
    allocationCost t a x = u := by
  exact ((allocation_inverse_iff ht ha hu hx0 hx1).2 hcoordinate).symm

/-- The explicitly constructed coordinate belongs to the domain in
`eq:allocation-x`, including when the original allocation is zero. -/
theorem allocationCoordinate_range {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) :
    0 ≤ allocationCoordinate t a u ∧ allocationCoordinate t a u < 1 := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  obtain ⟨hr0, hr1⟩ := allocation_ratio_range hc hu
  have hs1 : Real.sqrt (u / (u + t ^ 2 * a ^ 2)) < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hr0 hr1
  have hs2 : Real.sqrt (Real.sqrt (u / (u + t ^ 2 * a ^ 2))) < 1 := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (Real.sqrt_nonneg _) hs1
  exact ⟨Real.sqrt_nonneg _, hs2⟩

/-- The constructor satisfies the original fourth-power coordinate equation. -/
theorem allocationCoordinate_fourth {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) :
    (allocationCoordinate t a u) ^ 4 = u / (u + t ^ 2 * a ^ 2) := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  have hr0 := (allocation_ratio_range hc hu).1
  unfold allocationCoordinate
  calc
    Real.sqrt (Real.sqrt (u / (u + t ^ 2 * a ^ 2))) ^ 4 =
        (Real.sqrt (Real.sqrt (u / (u + t ^ 2 * a ^ 2))) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (u / (u + t ^ 2 * a ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
    _ = u / (u + t ^ 2 * a ^ 2) := Real.sq_sqrt hr0

/-- Passing from an original allocation to its explicit coordinate and back
recovers that allocation. -/
theorem allocationCost_coordinate {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) :
    allocationCost t a (allocationCoordinate t a u) = u := by
  obtain ⟨hx0, hx1⟩ := allocationCoordinate_range ht ha hu
  exact allocationCost_of_ratio ht ha hu hx0 hx1
    (allocationCoordinate_fourth ht ha hu).symm

/-- Passing from a transformed coordinate to its allocation and back recovers
the coordinate; the nonnegative fourth root is unique. -/
theorem allocationCoordinate_cost {t a x : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    allocationCoordinate t a (allocationCost t a x) = x := by
  have hu : 0 ≤ allocationCost t a x := allocationCost_nonneg hx0 hx1
  apply (pow_left_inj₀ (allocationCoordinate_range ht ha hu).1 hx0
    (by norm_num : (4 : ℕ) ≠ 0)).1
  rw [allocationCoordinate_fourth ht ha hu, allocationCost_ratio ht ha hx0 hx1]

/-- Pulling a common time factor out of the finite budget gives the displayed
constraint in `eq:allocation-x`. -/
theorem allocationCost_sum {ι : Type*} (s : Finset ι) (t : ℝ) (a x : ι → ℝ) :
    (∑ i ∈ s, allocationCost t (a i) (x i)) =
      t ^ 2 * ∑ i ∈ s, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold allocationCost
  ring

/-- The coordinate equations turn the original finite budget into exactly the
transformed constraint; all positivity assumptions are discharged pointwise. -/
theorem allocation_budget_eq {ι : Type*} (s : Finset ι) (t : ℝ)
    (a u x : ι → ℝ) (ht : 0 < t)
    (ha : ∀ i ∈ s, 0 < a i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i < 1)
    (hcoordinate : ∀ i ∈ s, u i / (u i + t ^ 2 * (a i) ^ 2) = (x i) ^ 4) :
    (∑ i ∈ s, u i) =
      t ^ 2 * ∑ i ∈ s, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
  calc
    (∑ i ∈ s, u i) = ∑ i ∈ s, allocationCost t (a i) (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (allocation_inverse_iff ht (ha i hi) (hu i hi) (hx0 i hi) (hx1 i hi)).2
        (hcoordinate i hi)
    _ = _ := allocationCost_sum s t a x

/-- In particular, the allocation simplex inequality and the transformed budget
inequality are equivalent under the actual coordinate map. -/
theorem allocation_budget_le_one_iff {ι : Type*} (s : Finset ι) (t : ℝ)
    (a u x : ι → ℝ) (ht : 0 < t)
    (ha : ∀ i ∈ s, 0 < a i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i < 1)
    (hcoordinate : ∀ i ∈ s, u i / (u i + t ^ 2 * (a i) ^ 2) = (x i) ^ 4) :
    (∑ i ∈ s, u i) ≤ 1 ↔
      t ^ 2 * (∑ i ∈ s, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤ 1 := by
  rw [allocation_budget_eq s t a u x ht ha hu hx0 hx1 hcoordinate]

/-- An actual original allocation supplies every hypothesis of the transformed
budget identity through `allocationCoordinate`; no coordinate certificate is
left to the caller. -/
theorem allocation_constructed_budget_eq {ι : Type*} (s : Finset ι) (t : ℝ)
    (a u : ι → ℝ) (ht : 0 < t)
    (ha : ∀ i ∈ s, 0 < a i) (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, u i) = t ^ 2 *
      ∑ i ∈ s, (a i) ^ 2 * (allocationCoordinate t (a i) (u i)) ^ 4 /
        (1 - (allocationCoordinate t (a i) (u i)) ^ 4) := by
  apply allocation_budget_eq s t a u (fun i => allocationCoordinate t (a i) (u i))
    ht ha hu
  · intro i hi
    exact (allocationCoordinate_range ht (ha i hi) (hu i hi)).1
  · intro i hi
    exact (allocationCoordinate_range ht (ha i hi) (hu i hi)).2
  · intro i hi
    exact (allocationCoordinate_fourth ht (ha i hi) (hu i hi)).symm

/-- Exact correspondence between the transformed feasible set and the image of
the original allocation simplex.  This is the feasible-set connection needed
when changing variables in the maximization defining the manuscript's `D_a`.
The witness in the reverse map is the explicit function `allocationCost`. -/
theorem allocation_feasible_image_iff {ι : Type*} (s : Finset ι) (t : ℝ)
    (a x : ι → ℝ) (ht : 0 < t) (ha : ∀ i ∈ s, 0 < a i) :
    ((∀ i ∈ s, 0 ≤ x i ∧ x i < 1) ∧
      t ^ 2 * (∑ i ∈ s, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤ 1) ↔
      ∃ u : ι → ℝ, (∀ i ∈ s, 0 ≤ u i) ∧ (∑ i ∈ s, u i) ≤ 1 ∧
        ∀ i ∈ s, allocationCoordinate t (a i) (u i) = x i := by
  constructor
  · rintro ⟨hx, hbudget⟩
    refine ⟨fun i => allocationCost t (a i) (x i), ?_, ?_, ?_⟩
    · intro i hi
      exact allocationCost_nonneg (hx i hi).1 (hx i hi).2
    · rw [allocationCost_sum]
      exact hbudget
    · intro i hi
      exact allocationCoordinate_cost ht (ha i hi) (hx i hi).1 (hx i hi).2
  · rintro ⟨u, hu, hbudget, hcoordinate⟩
    have hx : ∀ i ∈ s, 0 ≤ x i ∧ x i < 1 := by
      intro i hi
      rw [← hcoordinate i hi]
      exact allocationCoordinate_range ht (ha i hi) (hu i hi)
    refine ⟨hx, ?_⟩
    have hbudget_eq := allocation_budget_eq s t a u x ht ha hu
      (fun i hi => (hx i hi).1) (fun i hi => (hx i hi).2) (by
        intro i hi
        rw [← hcoordinate i hi]
        exact (allocationCoordinate_fourth ht (ha i hi) (hu i hi)).symm)
    rw [← hbudget_eq]
    exact hbudget

/-- Substitution of the pointwise KKT relation into the cost. -/
theorem allocationCost_eq_of_stationarity {t a x β : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hstationary : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) :
    allocationCost t a x = t ^ 2 * β * (a * x * (1 - x ^ 4)) := by
  have hden : 1 - x ^ 4 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hx0 hx1))
  unfold allocationCost
  calc
    t ^ 2 * a ^ 2 * x ^ 4 / (1 - x ^ 4) =
        t ^ 2 * a * x * (a * x ^ 3) / (1 - x ^ 4) := by ring
    _ = t ^ 2 * a * x * (β * (1 - x ^ 4) ^ 2) / (1 - x ^ 4) := by
      rw [hstationary]
    _ = t ^ 2 * β * (a * x * (1 - x ^ 4)) := by
      field_simp [hden]

/-- The pointwise stationarity equations imply the finite-sum KKT budget
identity, before imposing budget saturation. -/
theorem allocation_stationary_budget_eq {ι : Type*} (s : Finset ι)
    (t β : ℝ) (a x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i < 1)
    (hstationary : ∀ i ∈ s,
      a i * (x i) ^ 3 = β * (1 - (x i) ^ 4) ^ 2) :
    (∑ i ∈ s, allocationCost t (a i) (x i)) =
      t ^ 2 * β * ∑ i ∈ s, a i * x i * (1 - (x i) ^ 4) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact allocationCost_eq_of_stationarity (hx0 i hi) (hx1 i hi) (hstationary i hi)

/-- The second identity of `eq:allocation-kkt` follows from pointwise
stationarity and the saturated original allocation budget. -/
theorem allocation_kkt_budget {ι : Type*} (s : Finset ι)
    (t β : ℝ) (a u x : ι → ℝ) (ht : 0 < t)
    (ha : ∀ i ∈ s, 0 < a i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i < 1)
    (hcoordinate : ∀ i ∈ s, u i / (u i + t ^ 2 * (a i) ^ 2) = (x i) ^ 4)
    (hstationary : ∀ i ∈ s,
      a i * (x i) ^ 3 = β * (1 - (x i) ^ 4) ^ 2)
    (hsaturated : (∑ i ∈ s, u i) = 1) :
    1 = t ^ 2 * β * ∑ i ∈ s, a i * x i * (1 - (x i) ^ 4) := by
  calc
    1 = ∑ i ∈ s, u i := hsaturated.symm
    _ = ∑ i ∈ s, allocationCost t (a i) (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (allocation_inverse_iff ht (ha i hi) (hu i hi) (hx0 i hi) (hx1 i hi)).2
        (hcoordinate i hi)
    _ = _ := allocation_stationary_budget_eq s t β a x hx0 hx1 hstationary

/-- A caller using the original allocation variables only needs to provide its
stationarity equations and saturated budget.  The coordinate constructor
discharges the inverse-map and range hypotheses of `allocation_kkt_budget`. -/
theorem allocation_constructed_kkt_budget {ι : Type*} (s : Finset ι)
    (t β : ℝ) (a u : ι → ℝ) (ht : 0 < t)
    (ha : ∀ i ∈ s, 0 < a i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hstationary : ∀ i ∈ s,
      a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
        β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2)
    (hsaturated : (∑ i ∈ s, u i) = 1) :
    1 = t ^ 2 * β * ∑ i ∈ s,
      a i * allocationCoordinate t (a i) (u i) *
        (1 - (allocationCoordinate t (a i) (u i)) ^ 4) := by
  apply allocation_kkt_budget s t β a u
    (fun i => allocationCoordinate t (a i) (u i)) ht ha hu
  · intro i hi
    exact (allocationCoordinate_range ht (ha i hi) (hu i hi)).1
  · intro i hi
    exact (allocationCoordinate_range ht (ha i hi) (hu i hi)).2
  · intro i hi
    exact (allocationCoordinate_fourth ht (ha i hi) (hu i hi)).symm
  · exact hstationary
  · exact hsaturated

end IdentityTesting
