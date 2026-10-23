import IdentityTesting.OracleBudgetFamily
import IdentityTesting.OracleAggregateElasticity
import IdentityTesting.RationalAllocationOracleComparison

/-! The integrated parameter ratios, proved algebraically from the coordinate equation. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem stationary_coordinate_cubic_ratio {a β γ x y : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hsx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hsy : a * y ^ 3 = γ * (1 - y ^ 4) ^ 2) :
    y ≤ (γ / β) ^ (1 / 3 : ℝ) * x := by
  have hγ := hβ.trans_le hβγ
  have hxy := stationary_coordinate_parameter_mono ha hx.1 hx.2 hy.1 hy.2 hβγ hsx hsy
  have hd : (1 - y ^ 4) ^ 2 ≤ (1 - x ^ 4) ^ 2 := by
    apply pow_le_pow_left₀ (sub_pos.mpr (allocation_fourth_lt_one hy.1.le hy.2)).le
    have hh := pow_le_pow_left₀ hx.1.le hxy 4
    linarith only [hh]
  have hb : β * y ^ 3 ≤ γ * x ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hβ.le hγ.le)
    have hl : a * (β * y ^ 3) = β * γ * (1 - y ^ 4) ^ 2 := by rw [mul_left_comm a β, hsy]; ring
    have hr : a * (γ * x ^ 3) = β * γ * (1 - x ^ 4) ^ 2 := by rw [mul_left_comm a γ, hsx]; ring
    exact (mul_le_mul_iff_right₀ ha).mp (by rw [hl, hr]; exact hm)
  have hc : ((γ / β) ^ (1 / 3 : ℝ)) ^ 3 = γ / β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hγ hβ).le]
    norm_num
  apply (pow_le_pow_iff_left₀ hy.1.le (mul_nonneg (Real.rpow_nonneg (div_pos hγ hβ).le _) hx.1.le)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [mul_pow, hc]
  apply (mul_le_mul_iff_right₀ hβ).mp
  calc
    β * y ^ 3 ≤ γ * x ^ 3 := hb
    _ = β * (γ / β * x ^ 3) := by field_simp

theorem allocationCost_sq_stationary {t a β x : ℝ} (hx : 0 < x ∧ x < 1)
    (hs : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) :
    allocationCost t a x ^ 2 = t ^ 4 * a ^ 3 * β * x ^ 5 := by
  have hd : 1 - x ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hx.1.le hx.2))
  have heq : β = a * x ^ 3 / (1 - x ^ 4) ^ 2 := (eq_div_iff (pow_ne_zero 2 hd)).2 hs.symm
  rw [heq]
  unfold allocationCost
  field_simp
  <;> ring

theorem stationary_budget_sqrt_ratio {a β γ x y t : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hsx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hsy : a * y ^ 3 = γ * (1 - y ^ 4) ^ 2) :
    Real.sqrt (γ / β) * allocationCost t a x ≤ allocationCost t a y := by
  have hγ := hβ.trans_le hβγ
  have hxy := stationary_coordinate_parameter_mono ha hx.1 hx.2 hy.1 hy.2 hβγ hsx hsy
  have hcx : 0 ≤ allocationCost t a x := by
    unfold allocationCost
    exact div_nonneg (by positivity) (sub_pos.mpr (allocation_fourth_lt_one hx.1.le hx.2)).le
  have hcy : 0 ≤ allocationCost t a y := by
    unfold allocationCost
    exact div_nonneg (by positivity) (sub_pos.mpr (allocation_fourth_lt_one hy.1.le hy.2)).le
  apply (pow_le_pow_iff_left₀ (mul_nonneg (Real.sqrt_nonneg _) hcx) hcy
    (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, Real.sq_sqrt (div_pos hγ hβ).le,
    allocationCost_sq_stationary hx hsx, allocationCost_sq_stationary hy hsy]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1.le hxy 5)
    (show 0 ≤ t ^ 4 * a ^ 3 * γ by positivity)
  calc
    γ / β * (t ^ 4 * a ^ 3 * β * x ^ 5) = t ^ 4 * a ^ 3 * γ * x ^ 5 := by field_simp
    _ ≤ _ := hp

theorem realOracle_parameter_ratios {k : ℕ} (a : Fin k → ℝ) {β γ t : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hβγ : β ≤ γ) :
    Real.sqrt (γ / β) * realOracleBudget a t β ≤ realOracleBudget a t γ ∧
    realOracleObjective a γ ≤ (γ / β) ^ (1 / 3 : ℝ) * realOracleObjective a β := by
  have hγ := hβ.trans_le hβγ
  constructor
  · unfold realOracleBudget
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => stationary_budget_sqrt_ratio (ha i) hβ hβγ
      (realOracleCoordinate_spec (ha i) hβ).1 (realOracleCoordinate_spec (ha i) hγ).1
      (realOracleCoordinate_spec (ha i) hβ).2 (realOracleCoordinate_spec (ha i) hγ).2)
  · unfold realOracleObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (stationary_coordinate_cubic_ratio (ha i) hβ hβγ
      (realOracleCoordinate_spec (ha i) hβ).1 (realOracleCoordinate_spec (ha i) hγ).1
      (realOracleCoordinate_spec (ha i) hβ).2 (realOracleCoordinate_spec (ha i) hγ).2) (ha i).le
    nlinarith only [h]

theorem realOracle_parameter_budget_ratios {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {β γ t : ℝ} (ha : ∀ i, 0 < a i)
    (ht : 0 < t) (hβ : 0 < β) (hβγ : β ≤ γ) :
    γ / β ≤ (realOracleBudget a t γ / realOracleBudget a t β) ^ 2 ∧
    realOracleObjective a γ / realOracleObjective a β ≤
      (realOracleBudget a t γ / realOracleBudget a t β) ^ (2 / 3 : ℝ) := by
  have hγ := hβ.trans_le hβγ
  have hQβ := realOracleBudget_pos a ha ht hβ
  have hQγ := realOracleBudget_pos a ha ht hγ
  have hJβ := realOracleObjective_pos a ha hβ
  have hh := realOracle_parameter_ratios a ha hβ hβγ (t := t)
  have hs : Real.sqrt (γ / β) ≤ realOracleBudget a t γ / realOracleBudget a t β :=
    (le_div_iff₀ hQβ).2 hh.1
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt (div_pos hγ hβ).le] at hsq
  refine ⟨hsq, ?_⟩
  have hJ := (div_le_iff₀ hJβ).2 hh.2
  have hpow := Real.rpow_le_rpow (div_pos hγ hβ).le hsq (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have heq : ((realOracleBudget a t γ / realOracleBudget a t β) ^ 2) ^ (1 / 3 : ℝ) =
      (realOracleBudget a t γ / realOracleBudget a t β) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hQγ hQβ).le]
    norm_num
  rw [heq] at hpow
  exact hJ.trans hpow

end IdentityTesting.RationalComputation
