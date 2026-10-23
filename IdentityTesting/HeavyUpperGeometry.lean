import IdentityTesting.FiniteAllocationUpper

/-! Allocation geometry for nonnegative tail weights. No probability
normalization is needed, so the distinguished head is removed before KKT. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper

structure TailWeights (Ω : Type*) where
  mass : Ω → ℝ
  nonneg : ∀ i, 0 ≤ mass i

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def coarseDisplacement (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ coarseLabels x η, q.mass i * x i

def concentratedResidual (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ concentratedLabels x η, q.mass i * (1 - x i)

def upperGap (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  coarseDisplacement q x η + concentratedResidual q x η

def coarseWeightSum (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ coarseLabels x η, q.mass i ^ ((2 : ℝ) / 3)

def weightedMoment (q : TailWeights Ω) (L : Finset Ω) : ℝ :=
  ∑ i ∈ L, q.mass i * Real.sqrt (q.mass i)

theorem weightedMoment_nonneg (q : TailWeights Ω) (L : Finset Ω) :
    0 ≤ weightedMoment q L :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i) (Real.sqrt_nonneg _))

theorem coarseDisplacement_nonneg (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ coarseDisplacement q x η :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i) (hx i))

theorem concentratedResidual_nonneg (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, x i ≤ 1) : 0 ≤ concentratedResidual q x η :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i) (sub_nonneg.mpr (hx i)))

theorem upperGap_nonneg (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : 0 ≤ upperGap q x η :=
  add_nonneg (coarseDisplacement_nonneg q x η (fun i => (hx i).1))
    (concentratedResidual_nonneg q x η (fun i => (hx i).2))

theorem budget_sum_le_gap (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∑ i, q.mass i * x i * (1 - x i ^ 4)) ≤ 4 * upperGap q x η := by
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
  have hD := coarseDisplacement_nonneg q x η (fun i => (hx i).1)
  dsimp [upperGap]
  linarith

theorem kkt_budget_gap (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hβ : 0 ≤ β)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4)) :
    1 ≤ 4 * T ^ 2 * β * upperGap q x η := by
  have h := mul_le_mul_of_nonneg_left (budget_sum_le_gap q x η hx)
    (mul_nonneg (sq_nonneg T) hβ)
  rw [← hbudget] at h
  nlinarith only [h]

theorem coarseWeightSum_cubed (q : TailWeights Ω) (x : Ω → ℝ) (η β : ℝ)
    (hη : 0 < η) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2) :
    coarseWeightSum q x η ^ 3 * (β * η ^ 2) ≤ coarseDisplacement q x η ^ 3 := by
  apply sum_cube_scaled_le (coarseLabels x η) _ _ (β * η ^ 2) (by positivity)
    (fun i _ => Real.rpow_nonneg (q.nonneg i) _)
    (fun i _ => mul_nonneg (q.nonneg i) (hx i).1)
  intro i hi
  have hp : (q.mass i ^ ((2 : ℝ) / 3)) ^ 3 = q.mass i ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (q.nonneg i)]
    norm_num
  rw [hp]
  have hd := coarse_kkt_denominator x η hx i hi
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hd 2) hβ.le
  rw [← hkkt i] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (q.mass i))
  nlinarith only [hm]

theorem coarseWeightSum_nonneg (q : TailWeights Ω) (x : Ω → ℝ) (η : ℝ) :
    0 ≤ coarseWeightSum q x η :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)

theorem coarseWeightSum_cubed_gap (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : 0 < η) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4)) :
    coarseWeightSum q x η ^ 3 * η ^ 2 ≤ 4 * T ^ 2 * upperGap q x η ^ 4 := by
  have hG := upperGap_nonneg q x η hx
  have hD := coarseDisplacement_nonneg q x η (fun i => (hx i).1)
  have hE := concentratedResidual_nonneg q x η (fun i => (hx i).2)
  have hDG : coarseDisplacement q x η ≤ upperGap q x η := by dsimp [upperGap]; linarith
  have hc := (coarseWeightSum_cubed q x η β hη hβ hx hkkt).trans
    (pow_le_pow_left₀ hD hDG 3)
  have hb := kkt_budget_gap q x η T β hx hβ.le hbudget
  have hm := mul_le_mul_of_nonneg_right hb
    (mul_nonneg (pow_nonneg (coarseWeightSum_nonneg q x η) 3) (sq_nonneg η))
  have hm' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 4 * T ^ 2 * upperGap q x η)
  nlinarith only [hm, hm']

theorem coarse_profile_norm_le (q : TailWeights Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : 0 < η) (hT : 0 < T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4)) :
    coarseWeightSum q x η ^ ((3 : ℝ) / 4) / Real.sqrt T ≤
      2 * upperGap q x η / Real.sqrt η := by
  have hS := coarseWeightSum_nonneg q x η
  have hG := upperGap_nonneg q x η hx
  have hp : (coarseWeightSum q x η ^ ((3 : ℝ) / 4)) ^ 4 = coarseWeightSum q x η ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS]
    norm_num
  have hηsq := Real.sq_sqrt hη.le
  have hTsq := Real.sq_sqrt hT.le
  have hraw := coarseWeightSum_cubed_gap q x η T β hη hβ hx hkkt hbudget
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hT) (Real.sqrt_pos.mpr hη)).2
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow, hp, show Real.sqrt η ^ 4 = η ^ 2 by nlinarith [sq_nonneg (Real.sqrt η ^ 2 - η)]]
  have hTr : (2 * upperGap q x η * Real.sqrt T) ^ 4 = 16 * upperGap q x η ^ 4 * T ^ 2 := by
    calc
      _ = 16 * upperGap q x η ^ 4 * (Real.sqrt T ^ 2) ^ 2 := by ring
      _ = _ := by rw [hTsq]
  rw [hTr]
  nlinarith only [hraw, mul_nonneg (sq_nonneg T) (pow_nonneg hG 4)]

theorem allocation_radius_split (q : TailWeights Ω) (x : Ω → ℝ) (η ε g : ℝ)
    (hradius : (∑ i, q.mass i * x i) + g = ε) :
    ε = coarseDisplacement q x η + (∑ i ∈ concentratedLabels x η, q.mass i) -
      concentratedResidual q x η + g := by
  rw [← hradius, split_sum x η]
  dsimp [coarseDisplacement, concentratedResidual]
  have heq : (∑ i ∈ concentratedLabels x η, (q.mass i - q.mass i * (1 - x i))) =
      ∑ i ∈ concentratedLabels x η, q.mass i * x i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_sub_distrib] at heq
  linarith

end IdentityTesting.HeavyUpper
