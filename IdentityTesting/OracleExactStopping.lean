import IdentityTesting.OracleParameterRatios
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Original ambiguous-budget and narrow-parameter error constants. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem stationaryBudget_le_parameter_mass {k : ℕ} (a x : Fin k → ℝ) {t β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hs : ∀ i, a i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2) :
    stationaryBudget a x t ≤ t ^ 2 * β * ∑ i, a i := by
  unfold stationaryBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd : 1 - x i ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one (hx i).1.le (hx i).2))
  have hb : β = a i * x i ^ 3 / (1 - x i ^ 4) ^ 2 := (eq_div_iff (pow_ne_zero 2 hd)).2 (hs i).symm
  have hcost : allocationCost t (a i) (x i) = t ^ 2 * β * a i * x i * (1 - x i ^ 4) := by
    rw [hb]
    unfold allocationCost
    field_simp
    <;> ring
  rw [hcost]
  have hfactor : x i * (1 - x i ^ 4) ≤ 1 := by
    have hh := mul_nonneg (hx i).1.le (pow_nonneg (hx i).1.le 4)
    nlinarith only [hh, (hx i).2.le]
  have hm := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ t ^ 2 * β * a i from mul_nonneg (mul_nonneg (sq_nonneg t) hβ.le) (ha i).le)
  nlinarith only [hm]

theorem realOracleObjective_le_mass {k : ℕ} (a : Fin k → ℝ) {β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) : realOracleObjective a β ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (realOracleCoordinate_spec (ha i) hβ).1.2.le (ha i).le).trans_eq (mul_one _)

theorem realOracle_exact_ambiguous_error {k : ℕ} (a : Fin k → ℝ) {t β γ ω : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hγ : 0 < γ) (hω : ω ≤ 1 / 100)
    (hQγ : realOracleBudget a t γ = 1)
    (hQβ : |realOracleBudget a t β - 1| ≤ ω) :
    |realOracleObjective a β - realOracleObjective a γ| ≤ 2 * (∑ i, a i) * ω := by
  have hx i := realOracleCoordinate_spec (ha i) hβ
  have hy i := realOracleCoordinate_spec (ha i) hγ
  have hbx := stationaryBudget_le_parameter_mass (t := t) a (fun i => realOracleCoordinate (a i) β)
    ha hβ (fun i => (hx i).1) (fun i => (hx i).2)
  have hby := stationaryBudget_le_parameter_mass (t := t) a (fun i => realOracleCoordinate (a i) γ)
    ha hγ (fun i => (hy i).1) (fun i => (hy i).2)
  change realOracleBudget a t β ≤ _ at hbx
  change realOracleBudget a t γ ≤ _ at hby
  have hlow := (abs_le.mp hQβ).1
  have hr : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => (ha i).le)
  exact stationary_ambiguous_budget ha (fun i => (hx i).1) (fun i => (hy i).1)
    (mul_nonneg (by norm_num) hr) (by nlinarith only [hbx, hlow, hω])
    (by rw [hQγ] at hby; nlinarith only [hby])
    (fun i => (hx i).2) (fun i => (hy i).2) hQγ hQβ

theorem realOracle_exact_narrow_error {k : ℕ} (a : Fin k → ℝ) {β γ ζ : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hβγ : β ≤ γ) (hζ : 0 ≤ ζ)
    (hwidth : γ / β ≤ 1 + ζ) :
    realOracleObjective a γ - realOracleObjective a β ≤ (∑ i, a i) * ζ / 3 := by
  have hγ := hβ.trans_le hβγ
  have hratio := (realOracle_parameter_ratios a ha hβ hβγ (t := 1)).2
  have hpow := Real.rpow_le_rpow (div_pos hγ hβ).le hwidth (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have htangent := rpow_one_add_le_one_add_mul_self (s := ζ) (by linarith)
    (p := (1 / 3 : ℝ)) (by norm_num) (by norm_num)
  have hJ : 0 ≤ realOracleObjective a β :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i).le (realOracleCoordinate_spec (ha i) hβ).1.1.le)
  have hm := mul_le_mul_of_nonneg_right (hpow.trans htangent) hJ
  have hmass := mul_le_mul_of_nonneg_left (realOracleObjective_le_mass a ha hβ) hζ
  nlinarith only [hratio, hm, hmass]

theorem realOracleBudget_value_at_one {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t β : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) (hβ : 0 < β)
    (hQ : realOracleBudget a t β = 1) :
    allocationD (extendFiniteVector a) t = realOracleObjective a β := by
  obtain ⟨γ, hγ, _⟩ := realOracleBudget_unique_optimizer a ha ht
  have heq := (realOracleBudget_strictMonoOn a ha ht).injOn hβ hγ.1 (hQ.trans hγ.2.1.symm)
  simpa only [heq] using hγ.2.2

theorem realOracle_ambiguous_clamped_interval {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t β σ l u : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t)
    (hβ : 0 < β) (hσ : 0 < σ) (hσr : σ ≤ ∑ i, a i)
    (hQ : |realOracleBudget a t β - 1| ≤ σ / (100 * ∑ i, a i))
    (hl : l ≤ realOracleObjective a β) (hu : realOracleObjective a β ≤ u)
    (hwidth : u - l ≤ σ / 100) :
    let r := ∑ i, a i
    let ω := σ / (100 * r)
    let L := max 0 (l - 2 * r * ω)
    let U := min r (u + 2 * r * ω)
    L ≤ allocationD (extendFiniteVector a) t ∧
      allocationD (extendFiniteVector a) t ≤ U ∧ U - L ≤ σ / 20 := by
  let r := ∑ i, a i
  let ω := σ / (100 * r)
  have hr : 0 < r := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hω : ω ≤ 1 / 100 := by
    apply (div_le_iff₀ (by positivity : 0 < 100 * r)).2
    change σ ≤ r at hσr
    linarith only [hσr]
  have hmul : r * ω = σ / 100 := by dsimp only [ω]; field_simp
  obtain ⟨γ, hγ, _⟩ := realOracleBudget_unique_optimizer a ha ht
  have herr := realOracle_exact_ambiguous_error a ha hβ hγ.1 hω hγ.2.1 hQ
  have hlower := (abs_le.mp herr).2
  have hupper := (abs_le.mp herr).1
  have hnonneg : 0 ≤ realOracleObjective a γ := (realOracleObjective_pos a ha hγ.1).le
  have hmass := realOracleObjective_le_mass a ha hγ.1
  change max 0 (l - 2 * r * ω) ≤ _ ∧ _ ≤ min r (u + 2 * r * ω) ∧
    min r (u + 2 * r * ω) - max 0 (l - 2 * r * ω) ≤ σ / 20
  rw [hγ.2.2]
  refine ⟨max_le hnonneg (by linarith only [hlower, hl]),
    le_min hmass (by linarith only [hupper, hu]), ?_⟩
  have hmin := min_le_right r (u + 2 * r * ω)
  have hmax := le_max_right 0 (l - 2 * r * ω)
  nlinarith only [hmin, hmax, hwidth, hmul]

end IdentityTesting.RationalComputation
