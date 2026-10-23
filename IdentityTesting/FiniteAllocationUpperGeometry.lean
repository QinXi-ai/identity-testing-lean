import IdentityTesting.AllocationFiniteBridge
import IdentityTesting.ProfileTesting

/-! Deterministic geometry of the actual finite allocation optimizer used by
the allocation upper bound. The hypotheses here are its algebraic KKT equations;
the final caller obtains those equations from the original allocation root. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def coarseLabels (x : Ω → ℝ) (η : ℝ) : Finset Ω :=
  Finset.univ.filter (fun i => x i < 1 - η)

def concentratedLabels (x : Ω → ℝ) (η : ℝ) : Finset Ω :=
  Finset.univ \ coarseLabels x η

def coarseDisplacement (q : Probability Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ coarseLabels x η, q.mass i * x i

def concentratedResidual (q : Probability Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ concentratedLabels x η, q.mass i * (1 - x i)

def upperGap (q : Probability Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  coarseDisplacement q x η + concentratedResidual q x η

def coarseWeightSum (q : Probability Ω) (x : Ω → ℝ) (η : ℝ) : ℝ :=
  ∑ i ∈ coarseLabels x η, q.mass i ^ ((2 : ℝ) / 3)

theorem unit_interval_powers {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 ≤ x ∧ x ^ 3 ≤ x ∧ x ^ 4 ≤ x := by
  have h2 : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have h3 : x ^ 3 ≤ x := by
    have h := mul_le_mul_of_nonneg_left h2 hx0
    nlinarith
  have h4 : x ^ 4 ≤ x := by
    have h := mul_le_mul_of_nonneg_left h3 hx0
    nlinarith
  exact ⟨h2, h3, h4⟩

theorem unit_interval_budget_term {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x ^ 4) ≤ 4 * (1 - x) := by
  obtain ⟨h2, h3, h4⟩ := unit_interval_powers hx0 hx1
  have hsum : x + x ^ 2 + x ^ 3 + x ^ 4 ≤ 4 := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hx1)
  nlinarith only [hm]

omit [DecidableEq Ω] in
theorem coarseDisplacement_nonneg (q : Probability Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ coarseDisplacement q x η :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i) (hx i))

theorem concentratedResidual_nonneg (q : Probability Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, x i ≤ 1) : 0 ≤ concentratedResidual q x η :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (q.nonneg i) (sub_nonneg.mpr (hx i)))

theorem upperGap_nonneg (q : Probability Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : 0 ≤ upperGap q x η :=
  add_nonneg (coarseDisplacement_nonneg q x η (fun i => (hx i).1))
    (concentratedResidual_nonneg q x η (fun i => (hx i).2))

theorem split_sum (x : Ω → ℝ) (η : ℝ) (f : Ω → ℝ) :
    (∑ i, f i) = (∑ i ∈ coarseLabels x η, f i) +
      ∑ i ∈ concentratedLabels x η, f i := by
  rw [concentratedLabels, add_comm]
  exact (Finset.sum_sdiff (Finset.subset_univ (coarseLabels x η))).symm

theorem budget_sum_le_gap (q : Probability Ω) (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    (∑ i, q.mass i * x i * (1 - x i ^ 4)) ≤ 4 * upperGap q x η := by
  rw [split_sum x η]
  have hh : (∑ i ∈ coarseLabels x η, q.mass i * x i * (1 - x i ^ 4)) ≤
      coarseDisplacement q x η := by
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_nonneg (mul_nonneg (q.nonneg i) (hx i).1) (pow_nonneg (hx i).1 4)
    nlinarith only [h]
  have hl : (∑ i ∈ concentratedLabels x η, q.mass i * x i * (1 - x i ^ 4)) ≤
      4 * concentratedResidual q x η := by
    rw [concentratedResidual, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (unit_interval_budget_term (hx i).1 (hx i).2)
      (q.nonneg i)
    nlinarith only [h]
  have hD := coarseDisplacement_nonneg q x η (fun i => (hx i).1)
  dsimp [upperGap]
  linarith

theorem kkt_budget_gap (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hβ : 0 ≤ β)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4)) :
    1 ≤ 4 * T ^ 2 * β * upperGap q x η := by
  have h := mul_le_mul_of_nonneg_left (budget_sum_le_gap q x η hx)
    (mul_nonneg (sq_nonneg T) hβ)
  rw [← hbudget] at h
  nlinarith only [h]

omit [DecidableEq Ω] in
theorem coarse_kkt_denominator (x : Ω → ℝ) (η : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (i : Ω) (hi : i ∈ coarseLabels x η) :
    η ≤ 1 - x i ^ 4 := by
  have hi' := (Finset.mem_filter.mp hi).2
  have h4 := (unit_interval_powers (hx i).1 (hx i).2).2.2
  linarith

omit [DecidableEq Ω] in
theorem coarse_kkt_scalar (q : Probability Ω) (x : Ω → ℝ) (η β : ℝ)
    (hη : 0 ≤ η) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (i : Ω) (hi : i ∈ coarseLabels x η) : β * η ^ 2 ≤ q.mass i * x i := by
  have hd := coarse_kkt_denominator x η hx i hi
  have hs := pow_le_pow_left₀ hη hd 2
  have hm := mul_le_mul_of_nonneg_left hs hβ
  rw [← hkkt i] at hm
  have hx3 := (unit_interval_powers (hx i).1 (hx i).2).2.1
  exact hm.trans (mul_le_mul_of_nonneg_left hx3 (q.nonneg i))

omit [DecidableEq Ω] in
theorem coarse_nonempty_kkt_beta (q : Probability Ω) (x : Ω → ℝ) (η β : ℝ)
    (hη : 0 ≤ η) (hβ : 0 ≤ β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hne : (coarseLabels x η).Nonempty) : β * η ^ 2 ≤ coarseDisplacement q x η := by
  obtain ⟨i, hi⟩ := hne
  exact (coarse_kkt_scalar q x η β hη hβ hx hkkt i hi).trans
    (Finset.single_le_sum (fun j _ => mul_nonneg (q.nonneg j) (hx j).1) hi)

theorem coarse_nonempty_reciprocal (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
    (hη : 0 < η) (hT : 0 < T) (hβ : 0 ≤ β)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hne : (coarseLabels x η).Nonempty) : η / 2 ≤ T * upperGap q x η := by
  have hG := upperGap_nonneg q x η hx
  have hE := concentratedResidual_nonneg q x η (fun i => (hx i).2)
  have hb := coarse_nonempty_kkt_beta q x η β hη.le hβ hx hkkt hne
  have hbG : β * η ^ 2 ≤ upperGap q x η := by dsimp [upperGap]; linarith
  have hbud := kkt_budget_gap q x η T β hx hβ hbudget
  have hm := mul_le_mul_of_nonneg_right hbud (sq_nonneg η)
  have hm' := mul_le_mul_of_nonneg_left hbG (by positivity : 0 ≤ 4 * T ^ 2 * upperGap q x η)
  have hsq : η ^ 2 ≤ 4 * (T * upperGap q x η) ^ 2 := by nlinarith only [hm, hm']
  nlinarith [mul_nonneg hT.le hG]

theorem sum_cube_scaled_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (B : ℝ)
    (hB : 0 < B) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hpoint : ∀ i ∈ s, a i ^ 3 * B ≤ b i ^ 3) :
    (∑ i ∈ s, a i) ^ 3 * B ≤ (∑ i ∈ s, b i) ^ 3 := by
  let c := B ^ ((1 : ℝ) / 3)
  have hc : 0 ≤ c := Real.rpow_nonneg hB.le _
  have hc3 : c ^ 3 = B := by
    dsimp [c]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    norm_num
  have hpoint' : ∀ i ∈ s, a i * c ≤ b i := by
    intro i hi
    apply (pow_le_pow_iff_left₀ (mul_nonneg (ha i hi) hc) (hb i hi) (by norm_num : (3 : ℕ) ≠ 0)).mp
    simpa only [mul_pow, hc3] using hpoint i hi
  have hs := Finset.sum_le_sum hpoint'
  rw [← Finset.sum_mul] at hs
  have hp := pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg ha) hc) hs 3
  simpa only [mul_pow, hc3] using hp

omit [DecidableEq Ω] in
theorem coarseWeightSum_cubed (q : Probability Ω) (x : Ω → ℝ) (η β : ℝ)
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

omit [DecidableEq Ω] in
theorem coarseWeightSum_nonneg (q : Probability Ω) (x : Ω → ℝ) (η : ℝ) :
    0 ≤ coarseWeightSum q x η :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)

theorem coarseWeightSum_cubed_gap (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
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

theorem coarse_profile_norm_le (q : Probability Ω) (x : Ω → ℝ) (η T β : ℝ)
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

theorem allocation_radius_split (q : Probability Ω) (x : Ω → ℝ) (η ε : ℝ)
    (hradius : (∑ i, q.mass i * x i) = ε) :
    ε = coarseDisplacement q x η + (∑ i ∈ concentratedLabels x η, q.mass i) -
      concentratedResidual q x η := by
  rw [← hradius, split_sum x η]
  dsimp [coarseDisplacement, concentratedResidual]
  have heq : (∑ i ∈ concentratedLabels x η, (q.mass i - q.mass i * (1 - x i))) =
      ∑ i ∈ concentratedLabels x η, q.mass i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [Finset.sum_sub_distrib] at heq
  linarith

end IdentityTesting.FiniteAllocationUpper
