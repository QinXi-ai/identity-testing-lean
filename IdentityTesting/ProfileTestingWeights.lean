import IdentityTesting.ProfileTestingMoments

/-! The actual two-thirds weights and light/heavy cutoff for the full-prefix test. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def tailLabels (a : Ω) : Finset Ω := Finset.univ.erase a
def powerWeight (q : Probability Ω) (i : Ω) : ℝ := q.mass i ^ ((2 : ℝ) / 3)
def weightSum (q : Probability Ω) (a : Ω) : ℝ := ∑ i ∈ tailLabels a, powerWeight q i
def profileRadius (q : Probability Ω) (a : Ω) (n : ℕ) : ℝ :=
  1 / (n : ℝ) + weightSum q a ^ ((3 : ℝ) / 4) / Real.sqrt n
def heavyLabels (q : Probability Ω) (a : Ω) (m : ℕ) : Finset Ω :=
  (tailLabels a).filter (fun i => 1 / ((m : ℝ) * Real.sqrt (weightSum q a)) ≤ powerWeight q i)
def lightLabels (q : Probability Ω) (a : Ω) (m : ℕ) : Finset Ω :=
  tailLabels a \ heavyLabels q a m

omit [DecidableEq Ω] in
theorem powerWeight_nonneg (q : Probability Ω) (i : Ω) : 0 ≤ powerWeight q i :=
  Real.rpow_nonneg (q.nonneg i) _

theorem weightSum_nonneg (q : Probability Ω) (a : Ω) : 0 ≤ weightSum q a :=
  Finset.sum_nonneg (fun i _ => powerWeight_nonneg q i)

theorem powerWeight_le_sum (q : Probability Ω) (a i : Ω) (hi : i ∈ tailLabels a) :
    powerWeight q i ≤ weightSum q a :=
  Finset.single_le_sum (fun j _ => powerWeight_nonneg q j) hi

omit [DecidableEq Ω] in
theorem powerWeight_sqrt (q : Probability Ω) (i : Ω) :
    powerWeight q i * Real.sqrt (powerWeight q i) = q.mass i := by
  unfold powerWeight
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (q.nonneg i)]
  rw [← Real.rpow_add_of_nonneg (q.nonneg i) (by norm_num) (by norm_num)]
  norm_num

omit [DecidableEq Ω] in
theorem powerWeight_ratio_sq (q : Probability Ω) (i : Ω) (hi : 0 < powerWeight q i) :
    q.mass i ^ 2 / powerWeight q i ^ 2 = powerWeight q i := by
  rw [← powerWeight_sqrt q i, mul_pow, Real.sq_sqrt hi.le]
  field_simp

theorem powerWeight_reference_bound (q : Probability Ω) (a i : Ω) (hi : i ∈ tailLabels a) :
    q.mass i ≤ Real.sqrt (weightSum q a) * powerWeight q i := by
  rw [← powerWeight_sqrt q i]
  have h := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (powerWeight_le_sum q a i hi)) (powerWeight_nonneg q i)
  simpa only [mul_comm] using h

theorem heavyLabels_subset (q : Probability Ω) (a : Ω) (m : ℕ) :
    heavyLabels q a m ⊆ tailLabels a := Finset.filter_subset _ _

theorem lightLabels_subset (q : Probability Ω) (a : Ω) (m : ℕ) :
    lightLabels q a m ⊆ tailLabels a := Finset.sdiff_subset

theorem heavy_weight_pos (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) (i : Ω) (hi : i ∈ heavyLabels q a m) :
    0 < powerWeight q i := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcut : 0 < 1 / ((m : ℝ) * Real.sqrt (weightSum q a)) := by positivity
  exact hcut.trans_le (Finset.mem_filter.mp hi).2

theorem heavy_weight_floor (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) (i : Ω) (hi : i ∈ heavyLabels q a m) :
    1 ≤ (m : ℝ) * Real.sqrt (weightSum q a) * powerWeight q i := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hden : 0 < (m : ℝ) * Real.sqrt (weightSum q a) := by positivity
  have h := (div_le_iff₀ hden).mp (Finset.mem_filter.mp hi).2
  nlinarith

theorem heavy_reference_square_sum (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) :
    (∑ i ∈ heavyLabels q a m, q.mass i ^ 2 / powerWeight q i ^ 2) ≤ weightSum q a := by
  calc
    _ = ∑ i ∈ heavyLabels q a m, powerWeight q i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact powerWeight_ratio_sq q i (heavy_weight_pos q a m hm hS i hi)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (heavyLabels_subset q a m)
      (fun i _ _ => powerWeight_nonneg q i)

theorem zero_reference_mem_light (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) (i : Ω) (hia : i ≠ a) (hi : q.mass i = 0) :
    i ∈ lightLabels q a m := by
  apply Finset.mem_sdiff.mpr
  constructor
  · simp [tailLabels, hia]
  · intro hh
    have hpos := heavy_weight_pos q a m hm hS i hh
    simp [powerWeight, hi] at hpos

theorem sqrt_cutoff_identity (S M : ℝ) (hS : 0 < S) (hM : 0 < M) :
    S * Real.sqrt (1 / (M * Real.sqrt S)) = S ^ ((3 : ℝ) / 4) / Real.sqrt M := by
  have hR : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hW : 0 < Real.sqrt (Real.sqrt S) := Real.sqrt_pos.mpr hR
  have hMroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hpow : Real.sqrt S * Real.sqrt (Real.sqrt S) = S ^ ((3 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le]
    rw [← Real.rpow_add_of_nonneg hS.le (by norm_num) (by norm_num)]
    norm_num
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    Real.sqrt_mul hM.le, ← hpow]
  apply (eq_div_iff (ne_of_gt hMroot)).2
  field_simp
  nlinarith [Real.sq_sqrt hS.le, Real.sq_sqrt hR.le]

theorem light_reference_mass_le (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) :
    eventMass q (lightLabels q a m) ≤ weightSum q a ^ ((3 : ℝ) / 4) / Real.sqrt m := by
  let c := 1 / ((m : ℝ) * Real.sqrt (weightSum q a))
  have hc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  calc
    _ ≤ ∑ i ∈ lightLabels q a m, Real.sqrt c * powerWeight q i := by
      apply Finset.sum_le_sum
      intro i hi
      have hit := (Finset.mem_sdiff.mp hi).1
      have hni := (Finset.mem_sdiff.mp hi).2
      have hw : powerWeight q i < c := by
        by_contra h
        exact hni (Finset.mem_filter.mpr ⟨hit, le_of_not_gt h⟩)
      rw [← powerWeight_sqrt q i]
      have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hw.le) (powerWeight_nonneg q i)
      simpa only [mul_comm] using hh
    _ = Real.sqrt c * ∑ i ∈ lightLabels q a m, powerWeight q i := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt c * weightSum q a := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (lightLabels_subset q a m)
        (fun i _ _ => powerWeight_nonneg q i)) hc
    _ = _ := by
      rw [mul_comm]
      exact sqrt_cutoff_identity _ _ hS (Nat.cast_pos.mpr hm)

end IdentityTesting.ProfileTesting
