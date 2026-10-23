import IdentityTesting.RationalAllocationOracleBounds

/-! Algebraic comparison bounds for the actual parameter search. These avoid
logarithmic differentiation, without changing the input allocation optimum. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def stationaryBudget {k : ℕ} (a x : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ i, allocationCost t (a i) (x i)

def stationaryObjective {k : ℕ} (a x : Fin k → ℝ) : ℝ := ∑ i, a i * x i

theorem stationary_sums_mono {k : ℕ} {a x y : Fin k → ℝ} {t β γ : ℝ}
    (ha : ∀ i, 0 < a i) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hβγ : β ≤ γ)
    (hsx : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hsy : ∀ i, a i * y i ^ 3 = γ * (1 - y i ^ 4) ^ 2) :
    stationaryBudget a x t ≤ stationaryBudget a y t ∧
      stationaryObjective a x ≤ stationaryObjective a y := by
  have hxy i := stationary_coordinate_parameter_mono (ha i) (hx i).1 (hx i).2
    (hy i).1 (hy i).2 hβγ (hsx i) (hsy i)
  constructor
  · exact Finset.sum_le_sum (fun i _ => allocationCost_mono (hx i).1.le (hxy i) (hy i).2)
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hxy i) (ha i).le)

theorem stationary_sums_tangent {k : ℕ} {a x y : Fin k → ℝ} {t β γ : ℝ}
    (ha : ∀ i, 0 < a i) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hβγ : β ≤ γ)
    (hsx : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hsy : ∀ i, a i * y i ^ 3 = γ * (1 - y i ^ 4) ^ 2) :
    4 * t ^ 2 * β * (stationaryObjective a y - stationaryObjective a x) ≤
      stationaryBudget a y t - stationaryBudget a x t := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    allocationCost_stationary_tangent (t := t) (hx i).1
      (stationary_coordinate_parameter_mono (ha i) (hx i).1 (hx i).2
        (hy i).1 (hy i).2 hβγ (hsx i) (hsy i)) (hy i).2 (hsx i))
  simpa only [stationaryObjective, stationaryBudget, mul_sub, Finset.sum_sub_distrib,
    ← Finset.mul_sum] using hsum

theorem stationary_objective_le_budget_gap {k : ℕ} {a x y : Fin k → ℝ} {t β γ r : ℝ}
    (ha : ∀ i, 0 < a i) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hβγ : β ≤ γ) (hr : 0 ≤ r)
    (hlower : 1 ≤ t ^ 2 * β * r)
    (hsx : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hsy : ∀ i, a i * y i ^ 3 = γ * (1 - y i ^ 4) ^ 2) :
    stationaryObjective a y - stationaryObjective a x ≤
      r * (stationaryBudget a y t - stationaryBudget a x t) := by
  have hJ := (stationary_sums_mono (t := t) ha hx hy hβγ hsx hsy).2
  have hd : 0 ≤ stationaryObjective a y - stationaryObjective a x := sub_nonneg.mpr hJ
  have hmul := mul_le_mul_of_nonneg_right hlower hd
  calc
    _ ≤ r * (4 * t ^ 2 * β * (stationaryObjective a y - stationaryObjective a x)) := by
      nlinarith only [hmul, hd]
    _ ≤ _ := mul_le_mul_of_nonneg_left (stationary_sums_tangent ha hx hy hβγ hsx hsy) hr

/-- A near-unit budget certifies proximity to the actual optimal objective.
Both beta lower bounds come from the fixed, computed initial bracket. -/
theorem stationary_ambiguous_budget {k : ℕ} {a x y : Fin k → ℝ} {t β γ r ω : ℝ}
    (ha : ∀ i, 0 < a i) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hy : ∀ i, 0 < y i ∧ y i < 1) (hr : 0 ≤ r)
    (hβlower : 1 ≤ t ^ 2 * β * r) (hγlower : 1 ≤ t ^ 2 * γ * r)
    (hsx : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hsy : ∀ i, a i * y i ^ 3 = γ * (1 - y i ^ 4) ^ 2)
    (hybudget : stationaryBudget a y t = 1)
    (hbudget : |stationaryBudget a x t - 1| ≤ ω) :
    |stationaryObjective a x - stationaryObjective a y| ≤ r * ω := by
  by_cases hβγ : β ≤ γ
  · obtain ⟨hQ, hJ⟩ := stationary_sums_mono (t := t) ha hx hy hβγ hsx hsy
    rw [hybudget] at hQ
    have h := stationary_objective_le_budget_gap ha hx hy hβγ hr hβlower hsx hsy
    rw [hybudget] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hJ)]
    rw [abs_of_nonpos (sub_nonpos.mpr hQ)] at hbudget
    have hm := mul_le_mul_of_nonneg_left hbudget hr
    linarith only [h, hm]
  · have hγβ : γ ≤ β := (lt_of_not_ge hβγ).le
    obtain ⟨hQ, hJ⟩ := stationary_sums_mono (t := t) ha hy hx hγβ hsy hsx
    rw [hybudget] at hQ
    have h := stationary_objective_le_budget_gap ha hy hx hγβ hr hγlower hsy hsx
    rw [hybudget] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hJ)]
    rw [abs_of_nonneg (sub_nonneg.mpr hQ)] at hbudget
    exact h.trans (mul_le_mul_of_nonneg_left hbudget hr)

/-- The looser algebraic ratio bound suffices for a polynomial parameter search. -/
theorem stationary_objective_narrow {k : ℕ} {a x y : Fin k → ℝ} {β γ ζ : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hβγ : β ≤ γ) (hζ : 0 ≤ ζ)
    (hwidth : γ - β ≤ ζ * β)
    (hx : ∀ i, 0 < x i ∧ x i < 1) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (hsx : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hsy : ∀ i, a i * y i ^ 3 = γ * (1 - y i ^ 4) ^ 2) :
    stationaryObjective a y - stationaryObjective a x ≤ (∑ i, a i) * ζ := by
  have hcoord (i : Fin k) : y i - x i ≤ ζ := by
    have hratio := stationary_coordinate_ratio (ha i) hβ hβγ (hx i).1 (hx i).2
      (hy i).1 (hy i).2 (hsx i) (hsy i)
    have hwidth' := mul_le_mul_of_nonneg_right hwidth (hx i).1.le
    have hunit := mul_le_mul_of_nonneg_left (hx i).2.le (mul_nonneg hζ hβ.le)
    have hmul : β * (y i - x i) ≤ β * ζ := by nlinarith only [hratio, hwidth', hunit]
    exact (mul_le_mul_iff_right₀ hβ).mp hmul
  unfold stationaryObjective
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_sub] using mul_le_mul_of_nonneg_left (hcoord i) (ha i).le

end IdentityTesting.RationalComputation
