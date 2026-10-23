import IdentityTesting.OracleCoordinateElasticity
import IdentityTesting.RationalAllocationOracleBounds

/-! Continuity, strict monotonicity, full range and the unique budget-one parameter. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace IdentityTesting.RationalComputation

def realOracleBudget {k : ℕ} (a : Fin k → ℝ) (t β : ℝ) : ℝ :=
  ∑ i, allocationCost t (a i) (realOracleCoordinate (a i) β)

def realOracleObjective {k : ℕ} (a : Fin k → ℝ) (β : ℝ) : ℝ :=
  ∑ i, a i * realOracleCoordinate (a i) β

theorem realOracleBudget_continuousAt {k : ℕ} (a : Fin k → ℝ) {t β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) : ContinuousAt (realOracleBudget a t) β := by
  apply tendsto_finset_sum Finset.univ
  intro i _
  exact (hasDerivAt_allocationCost_coordinate (t := t) (a := a i)
    (realOracleCoordinate_spec (ha i) hβ).1).continuousAt.comp
      (realOracleCoordinate_continuousAt (ha i) hβ)

theorem realOracleObjective_continuousAt {k : ℕ} (a : Fin k → ℝ) {β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) : ContinuousAt (realOracleObjective a) β := by
  apply tendsto_finset_sum Finset.univ
  intro i _
  exact continuousAt_const.mul (realOracleCoordinate_continuousAt (ha i) hβ)

theorem realOracleBudget_strictMonoOn {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    StrictMonoOn (realOracleBudget a t) (Set.Ioi 0) := by
  intro β hβ γ hγ hβγ
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hx := realOracleCoordinate_spec (ha i) hβ
  have hy := realOracleCoordinate_spec (ha i) hγ
  have hxy := realOracleCoordinate_strictMonoOn (ha i) hβ hγ hβγ
  have hdiff := allocationCost_difference (t := t) (a := a i) hx.1.1.le hxy.le hy.1.2
  have hp : 0 < realOracleCoordinate (a i) γ ^ 4 - realOracleCoordinate (a i) β ^ 4 :=
    sub_pos.mpr (by gcongr; exact hx.1.1.le)
  have hdl : 0 < 1 - realOracleCoordinate (a i) β ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx.1.1.le hx.1.2)
  have hdu : 0 < 1 - realOracleCoordinate (a i) γ ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hy.1.1.le hy.1.2)
  have hpos : 0 < t ^ 2 * a i ^ 2 *
      (realOracleCoordinate (a i) γ ^ 4 - realOracleCoordinate (a i) β ^ 4) /
      ((1 - realOracleCoordinate (a i) γ ^ 4) * (1 - realOracleCoordinate (a i) β ^ 4)) := by
    have hai := ha i
    positivity
  linarith only [hdiff, hpos]

theorem realOracleObjective_strictMonoOn {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    StrictMonoOn (realOracleObjective a) (Set.Ioi 0) := by
  intro β hβ γ hγ hβγ
  exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ =>
    mul_lt_mul_of_pos_left (realOracleCoordinate_strictMonoOn (ha i) hβ hγ hβγ) (ha i))

theorem realOracleBudget_surjective_positive {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t B : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) (hB : 0 < B) :
    ∃ β : ℝ, 0 < β ∧ realOracleBudget a t β = B := by
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  obtain ⟨x, β, hx, hβ, heq, hbudget, _⟩ :=
    exists_actual_oracle_optimizer a (t / Real.sqrt B) ha (div_pos ht hs) (Classical.arbitrary _)
  have hxcoord (i : Fin k) : x i = realOracleCoordinate (a i) β :=
    realOracleCoordinate_unique (ha i) hβ (hx i) (heq i)
  have hscale (i : Fin k) : allocationCost t (a i) (x i) =
      B * allocationCost (t / Real.sqrt B) (a i) (x i) := by
    unfold allocationCost
    rw [div_pow, Real.sq_sqrt hB.le]
    field_simp
  refine ⟨β, hβ, ?_⟩
  unfold realOracleBudget
  simp_rw [← hxcoord, hscale]
  rw [← Finset.mul_sum, hbudget, mul_one]

theorem realOracleBudget_nonneg {k : ℕ} (a : Fin k → ℝ) {t β : ℝ}
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) : 0 ≤ realOracleBudget a t β := by
  apply Finset.sum_nonneg
  intro i _
  have hx := realOracleCoordinate_spec (ha i) hβ
  unfold allocationCost
  exact div_nonneg (by positivity) (sub_nonneg.mpr (allocation_fourth_lt_one hx.1.1.le hx.1.2).le)

theorem realOracleBudget_tendsto_atTop {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    Tendsto (realOracleBudget a t) atTop atTop := by
  apply tendsto_atTop.2
  intro z
  obtain ⟨β, hβ, hQ⟩ := realOracleBudget_surjective_positive a ha ht
    (show (0 : ℝ) < max z 1 by positivity)
  filter_upwards [eventually_ge_atTop β] with γ hγ
  exact (le_max_left z 1).trans (hQ ▸
    (realOracleBudget_strictMonoOn a ha ht).monotoneOn hβ (hβ.trans_le hγ) hγ)

theorem realOracleBudget_tendsto_zero {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    Tendsto (realOracleBudget a t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨β, hβ, hQ⟩ := realOracleBudget_surjective_positive a ha ht (half_pos hε)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hβ)] with γ hγ hγβ
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (realOracleBudget_nonneg a ha hγ)]
  have h := (realOracleBudget_strictMonoOn a ha ht) hγ hβ hγβ
  rw [hQ] at h
  linarith

theorem realOracleBudget_unique_optimizer {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) {t : ℝ} (ha : ∀ i, 0 < a i) (ht : 0 < t) :
    ∃! β : ℝ, 0 < β ∧ realOracleBudget a t β = 1 ∧
      allocationD (extendFiniteVector a) t = realOracleObjective a β := by
  obtain ⟨x, β, hx, hβ, heq, hbudget, hvalue, _⟩ :=
    exists_actual_oracle_optimizer a t ha ht (Classical.arbitrary _)
  have hxcoord (i : Fin k) : x i = realOracleCoordinate (a i) β :=
    realOracleCoordinate_unique (ha i) hβ (hx i) (heq i)
  have hQ : realOracleBudget a t β = 1 := by
    unfold realOracleBudget
    simpa only [hxcoord] using hbudget
  refine ⟨β, ⟨hβ, hQ, ?_⟩, ?_⟩
  · simpa only [realOracleObjective, hxcoord] using hvalue
  · intro γ hγ
    exact (realOracleBudget_strictMonoOn a ha ht).injOn hγ.1 hβ (hγ.2.1.trans hQ.symm)

end IdentityTesting.RationalComputation
