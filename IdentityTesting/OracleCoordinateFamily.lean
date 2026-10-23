import IdentityTesting.RationalAllocationOracleScalar
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! The actual real coordinate family of the scalar allocation oracle. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting.RationalComputation

theorem exists_real_coordinate_root {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ y : ℝ, (0 < y ∧ y < 1) ∧ a * y ^ 3 = β * (1 - y ^ 4) ^ 2 := by
  let f : ℝ → ℝ := fun x => a * x ^ 3 - β * (1 - x ^ 4) ^ 2
  have hf : Continuous f := by fun_prop
  have h0 : f 0 ≤ 0 := by dsimp only [f]; nlinarith
  have h1 : 0 ≤ f 1 := by dsimp only [f]; nlinarith
  obtain ⟨y, hy, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ⟨h0, h1⟩
  have hy0 : y ≠ 0 := by intro hz; subst y; simp [f] at heq; linarith
  have hy1 : y ≠ 1 := by intro hz; subst y; simp [f] at heq; linarith
  exact ⟨y, ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hy1⟩,
    sub_eq_zero.mp heq⟩

def realOracleCoordinate (a β : ℝ) : ℝ :=
  if h : 0 < a ∧ 0 < β then (exists_real_coordinate_root h.1 h.2).choose else 0

theorem realOracleCoordinate_spec {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    (0 < realOracleCoordinate a β ∧ realOracleCoordinate a β < 1) ∧
    a * realOracleCoordinate a β ^ 3 = β * (1 - realOracleCoordinate a β ^ 4) ^ 2 := by
  rw [realOracleCoordinate, dif_pos ⟨ha, hβ⟩]
  exact (exists_real_coordinate_root ha hβ).choose_spec

theorem realOracleCoordinate_unique {a β y : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hy : 0 < y ∧ y < 1) (heq : a * y ^ 3 = β * (1 - y ^ 4) ^ 2) :
    y = realOracleCoordinate a β := by
  have h := realOracleCoordinate_spec ha hβ
  apply (coordinatePolynomial_strictMono ha hβ).injOn ⟨hy.1.le, hy.2.le⟩ ⟨h.1.1.le, h.1.2.le⟩
  dsimp only
  linarith only [heq, h.2]

theorem realOracleCoordinate_strictMonoOn {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (realOracleCoordinate a) (Set.Ioi 0) := by
  intro β hβ γ hγ hβγ
  have hx := realOracleCoordinate_spec ha hβ
  have hy := realOracleCoordinate_spec ha hγ
  have hle := stationary_coordinate_parameter_mono ha hx.1.1 hx.1.2 hy.1.1 hy.1.2 hβγ.le hx.2 hy.2
  apply lt_of_le_of_ne hle
  intro heq
  have hd : 0 < (1 - realOracleCoordinate a γ ^ 4) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr (allocation_fourth_lt_one hy.1.1.le hy.1.2))
  rw [heq] at hx
  nlinarith only [hx.2, hy.2, mul_pos (sub_pos.mpr hβγ) hd]

theorem realOracleCoordinate_continuousAt {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ContinuousAt (realOracleCoordinate a) β := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min (β / 2) (ε * β / 2), lt_min (half_pos hβ) (by positivity), ?_⟩
  intro γ hγdist
  rw [Real.dist_eq] at hγdist ⊢
  have hd1 := (lt_min_iff.mp hγdist).1
  have hd2 := (lt_min_iff.mp hγdist).2
  have hγ : 0 < γ := by have := (abs_lt.mp hd1).1; linarith
  have hx := realOracleCoordinate_spec ha hβ
  have hy := realOracleCoordinate_spec ha hγ
  by_cases hβγ : β ≤ γ
  · have hxy := stationary_coordinate_parameter_mono ha hx.1.1 hx.1.2 hy.1.1 hy.1.2 hβγ hx.2 hy.2
    have hrat := stationary_coordinate_ratio ha hβ hβγ hx.1.1 hx.1.2 hy.1.1 hy.1.2 hx.2 hy.2
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
    rw [abs_of_nonneg (sub_nonneg.mpr hβγ)] at hd2
    have hmul := mul_le_mul_of_nonneg_left hx.1.2.le (sub_nonneg.mpr hβγ)
    nlinarith only [hrat, hmul, hd2, hβ, hε]
  · have hγβ : γ ≤ β := le_of_lt (lt_of_not_ge hβγ)
    have hyx := stationary_coordinate_parameter_mono ha hy.1.1 hy.1.2 hx.1.1 hx.1.2 hγβ hy.2 hx.2
    have hrat := stationary_coordinate_ratio ha hγ hγβ hy.1.1 hy.1.2 hx.1.1 hx.1.2 hy.2 hx.2
    rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
    rw [abs_of_nonpos (sub_nonpos.mpr hγβ)] at hd2
    have hmul := mul_le_mul_of_nonneg_left hy.1.2.le (sub_nonneg.mpr hγβ)
    have hγhalf : β / 2 < γ := by have := (abs_lt.mp hd1).1; linarith
    have hdiff : 0 ≤ realOracleCoordinate a β - realOracleCoordinate a γ := sub_nonneg.mpr hyx
    have hm := mul_le_mul_of_nonneg_right hγhalf.le hdiff
    nlinarith only [hrat, hmul, hd2, hm, hβ]

end IdentityTesting.RationalComputation
