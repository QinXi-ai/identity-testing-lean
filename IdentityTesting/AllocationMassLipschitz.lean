import IdentityTesting.CountableAllocation
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Uniform mass stability of the original countable allocation supremum.
No normalization, positive-time, or positive-coordinate hypothesis is needed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

private theorem allocation_term_fourth {a t u : ℝ} (hu : 0 ≤ u) :
    (a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)) ^ 4 =
      a ^ 4 * u / (u + t ^ 2 * a ^ 2) := by
  have h := Real.rpow_inv_natCast_pow (x := u / (u + t ^ 2 * a ^ 2))
    (n := 4) (by positivity) (by norm_num)
  norm_num only [Nat.cast_ofNat] at h
  rw [mul_pow, h]
  ring

theorem allocation_term_mono_mass {a b t u : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) :
    a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤
      b * (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ) := by
  by_cases hz : u = 0
  · simp [hz]
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  have hb := ha.trans hab
  apply (pow_le_pow_iff_left₀ (allocation_term_bounds ha hu).1
    (allocation_term_bounds hb hu).1 (show (4 : ℕ) ≠ 0 by norm_num)).1
  rw [allocation_term_fourth hu, allocation_term_fourth hu]
  apply (div_le_div_iff₀ (by positivity : 0 < u + t ^ 2 * a ^ 2)
    (by positivity : 0 < u + t ^ 2 * b ^ 2)).2
  have hs : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have hf : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha hab 4
  have h1 := mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hf)
  have h2 := mul_nonneg (mul_nonneg (mul_nonneg hu (sq_nonneg t))
    (mul_nonneg (sq_nonneg a) (sq_nonneg b))) (sub_nonneg.mpr hs)
  nlinarith only [h1, h2]

private theorem allocation_term_ordered_diff {a b t u : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) :
    0 ≤ b * (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ) -
        a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ∧
      b * (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ) -
        a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤ b - a := by
  refine ⟨sub_nonneg.mpr (allocation_term_mono_mass ha hab hu), ?_⟩
  by_cases hz : u = 0
  · simp [hz, sub_nonneg.mpr hab]
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  have hs : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have hratio : (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ) ≤
      (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hu (by positivity)
    exact add_le_add_left (mul_le_mul_of_nonneg_left hs (sq_nonneg t)) u
  have hone : (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ) ≤ 1 := by
    apply Real.rpow_le_one (by positivity) _ (by norm_num)
    exact div_le_one_of_le₀ (le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg t) (sq_nonneg b))) (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hratio ha
  have h2 := mul_le_mul_of_nonneg_left hone (sub_nonneg.mpr hab)
  nlinarith only [h1, h2]

/-- The scalar summand is 1-Lipschitz in nonnegative mass, uniformly in time
and nonnegative allocation, including the zero-allocation case. -/
theorem allocation_term_abs_sub_le_mass {a b t u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) :
    |a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) -
      b * (u / (u + t ^ 2 * b ^ 2)) ^ (1 / 4 : ℝ)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · have h := allocation_term_ordered_diff (t := t) ha hab hu
    rw [abs_sub_comm, abs_of_nonneg h.1, abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    exact h.2
  · have h := allocation_term_ordered_diff (t := t) hb hba hu
    rw [abs_of_nonneg h.1, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact h.2

theorem countableAllocationObjective_abs_sub_le_mass {a b u : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hasum : Summable a) (hbsum : Summable b) (hu : ∀ i, 0 ≤ u i) :
    |countableAllocationObjective a t u - countableAllocationObjective b t u| ≤
      ∑' i, |a i - b i| := by
  have hfa := countableAllocationObjective_summable t ha hasum hu
  have hfb := countableAllocationObjective_summable t hb hbsum hu
  unfold countableAllocationObjective
  rw [← hfa.tsum_sub hfb]
  calc
    _ ≤ ∑' i, |a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ) -
        b i * (u i / (u i + t ^ 2 * b i ^ 2)) ^ (1 / 4 : ℝ)| := by
      have hnorm : Summable (fun i => ‖a i *
          (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ) -
          b i * (u i / (u i + t ^ 2 * b i ^ 2)) ^ (1 / 4 : ℝ)‖) := by
        simpa only [Real.norm_eq_abs] using (hfa.sub hfb).abs
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ _ := (hfa.sub hfb).abs.tsum_le_tsum
      (fun i => allocation_term_abs_sub_le_mass (ha i) (hb i) (hu i))
      (hasum.sub hbsum).abs

private theorem allocationD_le_add_mass_distance {a b : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hasum : Summable a) (hbsum : Summable b) :
    allocationD a t ≤ allocationD b t + ∑' i, |a i - b i| := by
  apply csSup_le (allocation_values_nonempty a t)
  rintro v ⟨u, hu, rfl⟩
  have h := countableAllocationObjective_abs_sub_le_mass t ha hb hasum hbsum hu.1
  have h' := countableAllocationObjective_le_allocationD t hb hbsum hu
  linarith [le_abs_self (countableAllocationObjective a t u -
    countableAllocationObjective b t u)]

/-- Uniform ℓ¹ stability of the actual supremum over all feasible allocations. -/
theorem allocationD_abs_sub_le_l1 {a b : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hasum : Summable a) (hbsum : Summable b) :
    |allocationD a t - allocationD b t| ≤ ∑' i, |a i - b i| := by
  have h1 := allocationD_le_add_mass_distance t ha hb hasum hbsum
  have h2 := allocationD_le_add_mass_distance t hb ha hbsum hasum
  have hsym : (∑' i, |b i - a i|) = ∑' i, |a i - b i| := by
    apply tsum_congr
    intro i
    exact abs_sub_comm _ _
  rw [hsym] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end IdentityTesting
