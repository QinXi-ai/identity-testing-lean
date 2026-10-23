import IdentityTesting.GeneralAllocationBounds
import IdentityTesting.DyadicGeometry

/-! Actual low/high partition, deletion set and numerical costs for the
all-radius allocation lower bound. -/

noncomputable section
namespace IdentityTesting.GeneralLowerGeometry
open scoped BigOperators
open Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lowCoords (x : ι → ℝ) : Finset ι := Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 8)
def highCoords (x : ι → ℝ) : Finset ι := (lowCoords x)ᶜ
def lowDisplacement (q x : ι → ℝ) : ℝ := ∑ i ∈ lowCoords x, q i * x i
def highDeficit (q x : ι → ℝ) : ℝ := ∑ i ∈ highCoords x, q i * (1 - x i)
def separationMargin (q x : ι → ℝ) : ℝ := lowDisplacement q x + highDeficit q x

@[simp] theorem mem_lowCoords (x : ι → ℝ) (i : ι) : i ∈ lowCoords x ↔ x i ≤ (1 : ℝ) / 8 := by
  simp [lowCoords]

@[simp] theorem mem_highCoords (x : ι → ℝ) (i : ι) : i ∈ highCoords x ↔ (1 : ℝ) / 8 < x i := by
  simp [highCoords]

theorem radius_partition (q x : ι → ℝ) :
    (∑ i, q i * x i) = lowDisplacement q x + (∑ i ∈ highCoords x, q i) - highDeficit q x := by
  have h := Finset.sum_add_sum_compl (lowCoords x) (fun i => q i * x i)
  have he : highDeficit q x = (∑ i ∈ highCoords x, q i) - ∑ i ∈ highCoords x, q i * x i := by
    simp [highDeficit, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  change _ = (∑ i ∈ lowCoords x, q i * x i) + _ - _
  dsimp only [highCoords]
  linarith

theorem separationMargin_pos [Nonempty ι] (q x : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hx : ∀ i, 0 < x i ∧ x i < 1) : 0 < separationMargin q x := by
  have hd : 0 ≤ lowDisplacement q x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hq i).le (hx i).1.le)
  have he : 0 ≤ highDeficit q x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hq i).le (sub_nonneg.mpr (hx i).2.le))
  by_cases hl : (lowCoords x).Nonempty
  · have hp : 0 < lowDisplacement q x := Finset.sum_pos (fun i _ => mul_pos (hq i) (hx i).1) hl
    exact add_pos_of_pos_of_nonneg hp he
  · have hh : (highCoords x).Nonempty := by
      simp only [highCoords, Finset.not_nonempty_iff_eq_empty.mp hl, Finset.compl_empty]
      exact Finset.univ_nonempty
    have hp : 0 < highDeficit q x :=
      Finset.sum_pos (fun i _ => mul_pos (hq i) (sub_pos.mpr (hx i).2)) hh
    exact add_pos_of_nonneg_of_pos hd hp

def deletedCoords (s : Finset ι) (q : ι → ℝ) (L : ℝ) : Finset ι :=
  s.filter (fun i => L / 1000000 < q i)

def retainedCoords (s : Finset ι) (q : ι → ℝ) (L : ℝ) : Finset ι :=
  s \ deletedCoords s q L

theorem retainedCoords_mass_le (s : Finset ι) (q : ι → ℝ) (L : ℝ)
    (i : ι) (hi : i ∈ retainedCoords s q L) : q i ≤ L / 1000000 := by
  obtain ⟨his, hid⟩ := Finset.mem_sdiff.mp hi
  by_contra hn
  exact hid (Finset.mem_filter.mpr ⟨his, lt_of_not_ge hn⟩)

/-- Deleting the actual masses above eta*L costs at most 128000/T. -/
theorem deleted_mass_rate (s : Finset ι) (q : ι → ℝ) (T L : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hT : 0 < T) (hL : 0 < L)
    (hmoment : T ^ 2 * (∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)) ^ 2 ≤ 16384 * L) :
    T * (∑ i ∈ deletedCoords s q L, q i) ≤ 128000 := by
  let D := deletedCoords s q L
  let d := ∑ i ∈ D, q i
  let A := ∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)
  have hd : 0 ≤ d := Finset.sum_nonneg (fun i _ => hq i)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hq i) _)
  have hcut : 0 ≤ L / 1000000 := by positivity
  have hsum : Real.sqrt (L / 1000000) * d ≤ A := by
    calc
      _ = ∑ i ∈ D, Real.sqrt (L / 1000000) * q i := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ D, (q i) ^ ((3 : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [allocation_three_halves_eq (hq i), mul_comm]
        apply mul_le_mul_of_nonneg_left _ (hq i)
        exact Real.sqrt_le_sqrt (Finset.mem_filter.mp hi).2.le
      _ ≤ A := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Real.rpow_nonneg (hq i) _)
  have hsq := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hd) hA).mpr hsum
  rw [mul_pow, Real.sq_sqrt hcut] at hsq
  have hscale := mul_le_mul_of_nonneg_left hsq (sq_nonneg T)
  have hmain : L * (T * d) ^ 2 ≤ L * (128000 : ℝ) ^ 2 := by
    nlinarith only [hscale, hmoment]
  have hsqTd := (mul_le_mul_left hL).mp hmain
  change T * d ≤ 128000
  nlinarith only [hsqTd]

/-- The actual manuscript sample regime makes the deterministic deletion cheap. -/
theorem deleted_sample_cost (s : Finset ι) (q : ι → ℝ) (T L : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hT : 0 < T) (hL : 0 < L)
    (hmoment : T ^ 2 * (∑ i ∈ s, (q i) ^ ((3 : ℝ) / 2)) ^ 2 ≤ 16384 * L)
    (n : ℕ) (hn : (n : ℝ) ≤ T / 1000000000000) :
    (n : ℝ) * (∑ i ∈ deletedCoords s q L, q i) ≤ (128000 : ℝ) / 1000000000000 := by
  have hd := Finset.sum_nonneg (fun i (_ : i ∈ deletedCoords s q L) => hq i)
  have hmul := mul_le_mul_of_nonneg_right hn hd
  have hrate := deleted_mass_rate s q T L hq hT hL hmoment
  nlinarith only [hmul, hrate]

theorem high_moment_le_margin (q x : ι → ℝ) (T : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hbudget : T ^ 2 * (∑ i, (q i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    T ^ 2 * (∑ i ∈ highCoords x, (q i) ^ ((3 : ℝ) / 2)) ^ 2 ≤
      16384 * separationMargin q x := by
  have h := allocation_high_subset_bound (highCoords x) q x hq hx
    (fun i hi => ((mem_highCoords x i).mp hi).le) hbudget
  have hd : 0 ≤ lowDisplacement q x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (hx i).1)
  change _ ≤ 16384 * highDeficit q x at h
  dsimp only [separationMargin]
  linarith

/-- The seed overlap estimate fits strictly inside the available radius margin. -/
theorem seed_overlap_lt_margin_fraction (A T L : ℝ) (hT : 0 < T) (hL : 0 < L)
    (hmoment : T ^ 2 * A ^ 2 ≤ 16384 * L)
    (n : ℕ) (hn : (n : ℝ) ≤ T / 1000000000000) :
    2 * 100000 * (n : ℝ) ^ 2 * A ^ 2 + 2 * (L / 1000000) < L / 100000 := by
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg n)
    (div_nonneg hT.le (by norm_num : (0 : ℝ) ≤ 1000000000000))).mpr hn
  have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg A)
  nlinarith only [hprod, hmoment, hL]

theorem paired_combined_cost_lt :
    (1 : ℝ) / 10 ^ 9 + 128000 / 1000000000000 + 1 / (2 * 100000) < 1 / 3 := by norm_num

theorem tilted_combined_cost_lt :
    (1 : ℝ) / 10 ^ 5 + 3 * (128000 / 1000000000000) + 9 / (2 * 100000) < 1 / 3 := by norm_num

end IdentityTesting.GeneralLowerGeometry
