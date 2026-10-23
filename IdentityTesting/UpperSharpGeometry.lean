import IdentityTesting.HeavyUpperConcentrated

/-! Sharp budget and moment constants for the concentrated-coordinate branch. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem budget_sum_le_displacement_residual (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∑ i, q.mass i * x i * (1 - x i ^ 4)) ≤
      coarseDisplacement q x η + 4 * concentratedResidual q x η := by
  rw [split_sum x η]
  have hh : (∑ i ∈ coarseLabels x η, q.mass i * x i * (1 - x i ^ 4)) ≤
      coarseDisplacement q x η := by
    apply Finset.sum_le_sum
    intro i _
    have h := mul_nonneg (mul_nonneg (q.nonneg i) (hx i).1) (pow_nonneg (hx i).1 4)
    nlinarith only [h]
  have hl : (∑ i ∈ concentratedLabels x η, q.mass i * x i * (1 - x i ^ 4)) ≤
      4 * concentratedResidual q x η := by
    rw [concentratedResidual, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (unit_interval_budget_term (hx i).1 (hx i).2)
      (q.nonneg i)
    nlinarith only [h]
  exact add_le_add hh hl

theorem concentrated_beta_moment_sharp (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (1 : ℝ) / 6 ≤ T ^ 2 * β * concentratedResidual q x η ∧
      T ^ 2 * β * concentratedResidual q x η ≤ 2 := by
  have hupper := budget_sum_le_displacement_residual q x η hx
  have hs : (∑ i, q.mass i * x i * (1 - x i ^ 4)) ≤
      6 * concentratedResidual q x η := by linarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ T ^ 2 * β)
  rw [← hbudget] at hm
  exact ⟨by nlinarith only [hm], (concentrated_beta_moment q x η T β hη hβ hx hbudget hD).2⟩

theorem concentrated_moment_scale_sharp (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (8 : ℝ) / 3 * concentratedResidual q x η ≤
        T ^ 2 * weightedMoment q (concentratedLabels x η) ^ 2 ∧
      T ^ 2 * weightedMoment q (concentratedLabels x η) ^ 2 ≤
        288 * concentratedResidual q x η := by
  have hE := concentratedResidual_nonneg q x η (fun i => (hx i).2)
  have hb := concentrated_beta_moment_sharp q x η T β hη hβ hx hbudget hD
  have ha := concentrated_weighted_mass_bounds q x η β hη hβ (fun i => (hx i).2) hkkt
  have hs := Real.sq_sqrt hβ
  have hlo := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * Real.sqrt β * concentratedResidual q x η) ha.1 2
  have hlo' := mul_le_mul_of_nonneg_left hlo (sq_nonneg T)
  have hb1 := mul_le_mul_of_nonneg_right hb.1 hE
  have heq : (4 * Real.sqrt β * concentratedResidual q x η) ^ 2 =
      16 * β * concentratedResidual q x η ^ 2 := by
    calc
      _ = 16 * Real.sqrt β ^ 2 * concentratedResidual q x η ^ 2 := by ring
      _ = _ := by rw [hs]
  rw [heq] at hlo'
  exact ⟨by nlinarith only [hlo', hb1],
    (concentrated_moment_scale q x η T β hη hβ hx hkkt hbudget hD).2⟩

end IdentityTesting.HeavyUpper

namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting CollisionTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem concentrated_beta_moment_sharp (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (1 : ℝ) / 6 ≤ T ^ 2 * β * concentratedResidual q x η ∧
      T ^ 2 * β * concentratedResidual q x η ≤ 2 :=
  HeavyUpper.concentrated_beta_moment_sharp ⟨q.mass, q.nonneg⟩ x η T β hη hβ hx hbudget hD

theorem concentrated_moment_scale_sharp (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : η ≤ 1 / 2) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hD : coarseDisplacement q x η ≤ 2 * concentratedResidual q x η) :
    (8 : ℝ) / 3 * concentratedResidual q x η ≤
        T ^ 2 * weightedMass q q (concentratedLabels x η) ^ 2 ∧
      T ^ 2 * weightedMass q q (concentratedLabels x η) ^ 2 ≤
        288 * concentratedResidual q x η :=
  HeavyUpper.concentrated_moment_scale_sharp ⟨q.mass, q.nonneg⟩ x η T β hη hβ hx hkkt hbudget hD

end IdentityTesting.FiniteAllocationUpper

