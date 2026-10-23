import IdentityTesting.HeavyUpperGeometry

/-! Weighted moment bounds for a finite tail allocation. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem concentrated_weighted_mass_bounds (q : TailWeights Ω) (x : Ω → ℝ) (η β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2) :
    4 * Real.sqrt β * concentratedResidual q x η ≤ weightedMoment q (concentratedLabels x η) ∧
      weightedMoment q (concentratedLabels x η) ≤ 12 * Real.sqrt β * concentratedResidual q x η := by
  constructor
  · rw [concentratedResidual, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := (kkt_sqrt_bounds (q.nonneg i) (concentrated_coordinate_bounds x η hη i hi).1
      (hx i) hβ (hkkt i)).1
    have h := mul_le_mul_of_nonneg_left hb (q.nonneg i)
    nlinarith only [h]
  · rw [concentratedResidual, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := (kkt_sqrt_bounds (q.nonneg i) (concentrated_coordinate_bounds x η hη i hi).1
      (hx i) hβ (hkkt i)).2
    have h := mul_le_mul_of_nonneg_left hb (q.nonneg i)
    nlinarith only [h]

theorem concentrated_sqrt_mass_le (q : TailWeights Ω) (x : Ω → ℝ) (η β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (i : Ω) (hi : i ∈ concentratedLabels x η) :
    Real.sqrt (q.mass i) ≤ 12 * η * Real.sqrt β := by
  have hc := concentrated_coordinate_bounds x η hη i hi
  have hb := (kkt_sqrt_bounds (q.nonneg i) hc.1 (hx i) hβ (hkkt i)).2
  have hm := mul_le_mul_of_nonneg_left hc.2 (by positivity : 0 ≤ 12 * Real.sqrt β)
  linarith

theorem concentrated_budget_lower (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hη : η ≤ 1 / 2) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    concentratedResidual q x η / 2 ≤ ∑ i, q.mass i * x i * (1 - x i ^ 4) := by
  have hp : ∀ i, 0 ≤ q.mass i * x i * (1 - x i ^ 4) := by
    intro i
    have h4 := (unit_interval_powers (hx i).1 (hx i).2).2.2
    have hd : 0 ≤ 1 - x i ^ 4 := by linarith [(hx i).2]
    exact mul_nonneg (mul_nonneg (q.nonneg i) (hx i).1) hd
  have hs : concentratedResidual q x η / 2 ≤
      ∑ i ∈ concentratedLabels x η, q.mass i * x i * (1 - x i ^ 4) := by
    rw [concentratedResidual, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hhalf := (concentrated_coordinate_bounds x η hη i hi).1
    have h4 := (unit_interval_powers (hx i).1 (hx i).2).2.2
    have h1 := mul_le_mul_of_nonneg_left (show 1 - x i ≤ 1 - x i ^ 4 by linarith) (hx i).1
    have h2 := mul_le_mul_of_nonneg_right hhalf (sub_nonneg.mpr (hx i).2)
    have h3 : (1 - x i) / 2 ≤ x i * (1 - x i ^ 4) := by linarith
    have hm := mul_le_mul_of_nonneg_left h3 (q.nonneg i)
    nlinarith only [hm]
  exact hs.trans (Finset.sum_le_univ_sum_of_nonneg hp)

theorem concentrated_beta_moment (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (1 : ℝ) / 12 ≤ T ^ 2 * β * concentratedResidual q x η ∧
      T ^ 2 * β * concentratedResidual q x η ≤ 2 := by
  have hgap := kkt_budget_gap q x η T β hx hβ hbudget
  have hgapbound : upperGap q x η ≤ 3 * concentratedResidual q x η := by
    dsimp [upperGap]
    linarith
  have hm := mul_le_mul_of_nonneg_left hgapbound (by positivity : 0 ≤ 4 * T ^ 2 * β)
  have hlo := mul_le_mul_of_nonneg_left (concentrated_budget_lower q x η hη hx)
    (by positivity : 0 ≤ T ^ 2 * β)
  rw [← hbudget] at hlo
  constructor <;> nlinarith only [hgap, hm, hlo]

theorem concentrated_moment_scale (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (4 : ℝ) / 3 * concentratedResidual q x η ≤
        T ^ 2 * weightedMoment q (concentratedLabels x η) ^ 2 ∧
      T ^ 2 * weightedMoment q (concentratedLabels x η) ^ 2 ≤
        288 * concentratedResidual q x η := by
  have hE := concentratedResidual_nonneg q x η (fun i => (hx i).2)
  have hA := weightedMoment_nonneg q (concentratedLabels x η)
  have hb := concentrated_beta_moment q x η T β hη hβ hx hbudget hD
  have ha := concentrated_weighted_mass_bounds q x η β hη hβ (fun i => (hx i).2) hkkt
  have hs := Real.sq_sqrt hβ
  have hlo := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * Real.sqrt β * concentratedResidual q x η) ha.1 2
  have hhi := pow_le_pow_left₀ hA ha.2 2
  have hlo' := mul_le_mul_of_nonneg_left hlo (sq_nonneg T)
  have hhi' := mul_le_mul_of_nonneg_left hhi (sq_nonneg T)
  have hb1 := mul_le_mul_of_nonneg_right hb.1 hE
  have hb2 := mul_le_mul_of_nonneg_right hb.2 hE
  have heq1 : (4 * Real.sqrt β * concentratedResidual q x η) ^ 2 =
      16 * β * concentratedResidual q x η ^ 2 := by calc
    _ = 16 * Real.sqrt β ^ 2 * concentratedResidual q x η ^ 2 := by ring
    _ = _ := by rw [hs]
  have heq2 : (12 * Real.sqrt β * concentratedResidual q x η) ^ 2 =
      144 * β * concentratedResidual q x η ^ 2 := by calc
    _ = 144 * Real.sqrt β ^ 2 * concentratedResidual q x η ^ 2 := by ring
    _ = _ := by rw [hs]
  rw [heq1] at hlo'
  rw [heq2] at hhi'
  constructor <;> nlinarith only [hlo', hhi', hb1, hb2]

end IdentityTesting.HeavyUpper
