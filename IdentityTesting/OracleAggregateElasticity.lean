import IdentityTesting.OracleBudgetFamily

/-! The logarithmic derivatives of Q and J are positive weighted averages. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem realOracleBudget_pos {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t β : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) (hβ : 0 < β) :
    0 < realOracleBudget a t β := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  have hai := ha i
  have hx := realOracleCoordinate_spec hai hβ
  have hxp := hx.1.1
  have hd := sub_pos.mpr (allocation_fourth_lt_one hx.1.1.le hx.1.2)
  unfold allocationCost
  positivity

theorem realOracleObjective_pos {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {β : ℝ} (ha : ∀ i, 0 < a i) (hβ : 0 < β) :
    0 < realOracleObjective a β := by
  exact Finset.sum_pos (fun i _ => mul_pos (ha i) (realOracleCoordinate_spec (ha i) hβ).1.1)
    Finset.univ_nonempty

theorem realOracleBudget_deriv {k : ℕ} (a : Fin k → ℝ) {t β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) :
    deriv (realOracleBudget a t) β =
      ∑ i, deriv (fun γ => allocationCost t (a i) (realOracleCoordinate (a i) γ)) β := by
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hasDerivAt_allocationCost_coordinate (t := t) (a := a i)
    (realOracleCoordinate_spec (ha i) hβ).1).comp β
      (realOracleCoordinate_hasDerivAt (ha i) hβ)).differentiableAt.hasDerivAt

theorem realOracleObjective_deriv {k : ℕ} (a : Fin k → ℝ) {β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) :
    deriv (realOracleObjective a) β = ∑ i, a i * deriv (realOracleCoordinate (a i)) β := by
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro i _
  exact (realOracleCoordinate_hasDerivAt (ha i) hβ).differentiableAt.hasDerivAt.const_mul (a i)

theorem realOracle_aggregate_elasticities {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t β : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) (hβ : 0 < β) :
    β * deriv (realOracleBudget a t) β / realOracleBudget a t β =
      (∑ i, allocationCost t (a i) (realOracleCoordinate (a i) β) *
        (4 / (3 + 5 * realOracleCoordinate (a i) β ^ 4))) / realOracleBudget a t β ∧
    β * deriv (realOracleObjective a) β / realOracleObjective a β =
      (∑ i, (a i * realOracleCoordinate (a i) β) *
        ((1 - realOracleCoordinate (a i) β ^ 4) /
          (3 + 5 * realOracleCoordinate (a i) β ^ 4))) / realOracleObjective a β := by
  have hcostpos (i : Fin k) : 0 < allocationCost t (a i) (realOracleCoordinate (a i) β) := by
    have hai := ha i
    have hx := realOracleCoordinate_spec hai hβ
    have hxp := hx.1.1
    have hd := sub_pos.mpr (allocation_fourth_lt_one hx.1.1.le hx.1.2)
    unfold allocationCost
    positivity
  constructor
  · rw [realOracleBudget_deriv a ha hβ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h := (realOracleCoordinate_elasticities (ha i) hβ ht).2
    exact (div_eq_iff (hcostpos i).ne').mp h |>.trans (mul_comm _ _)
  · rw [realOracleObjective_deriv a ha hβ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hx := realOracleCoordinate_spec (ha i) hβ
    have h := (div_eq_iff hx.1.1.ne').mp (realOracleCoordinate_elasticities (ha i) hβ ht).1
    nlinarith only [congrArg (fun z => a i * z) h]

private theorem weighted_average_mem_Icc {k : ℕ} (w v : Fin k → ℝ) {l u : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hs : 0 < ∑ i, w i) (hv : ∀ i, v i ∈ Set.Icc l u) :
    (∑ i, w i * v i) / (∑ i, w i) ∈ Set.Icc l u := by
  constructor
  · apply (le_div_iff₀ hs).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_left (hv i).1 (hw i)]
  · apply (div_le_iff₀ hs).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_left (hv i).2 (hw i)]

theorem realOracle_aggregate_elasticity_bounds {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t β : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) (hβ : 0 < β) :
    β * deriv (realOracleBudget a t) β / realOracleBudget a t β ∈ Set.Icc (1 / 2) (4 / 3) ∧
    β * deriv (realOracleObjective a) β / realOracleObjective a β ∈ Set.Icc 0 (1 / 3) := by
  rw [(realOracle_aggregate_elasticities a ha ht hβ).1,
    (realOracle_aggregate_elasticities a ha ht hβ).2]
  have hc i := realOracleCoordinate_elasticity_bounds (ha i) hβ ht
  have he i := realOracleCoordinate_elasticities (ha i) hβ ht
  simp only [(he _).1, (he _).2] at hc
  constructor
  · apply weighted_average_mem_Icc _ _ _ (realOracleBudget_pos a ha ht hβ) (fun i => (hc i).2)
    intro i
    have hx := realOracleCoordinate_spec (ha i) hβ
    unfold allocationCost
    exact div_nonneg (by positivity) (sub_pos.mpr (allocation_fourth_lt_one hx.1.1.le hx.1.2)).le
  · exact weighted_average_mem_Icc _ _
      (fun i => mul_nonneg (ha i).le (realOracleCoordinate_spec (ha i) hβ).1.1.le)
      (realOracleObjective_pos a ha hβ) (fun i => (hc i).1)

end IdentityTesting.RationalComputation
