import IdentityTesting.CountableRoots
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Sharp lower bounds on the actual allocation function and root. The feasible
allocation is the reference mass itself, including countable and zero-mass laws. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem reciprocal_quarter_rpow_tangent {x : ℝ} (hx : 0 ≤ x) :
    1 - x / 4 ≤ (1 / (1 + x)) ^ (1 / 4 : ℝ) := by
  have hb : 0 < 1 + x := by positivity
  have hy : 0 < (1 + x) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hb _
  have hu : (1 + x) ^ (1 / 4 : ℝ) ≤ 1 + x / 4 := by
    simpa only [show (1 / 4 : ℝ) * x = x / 4 by ring] using
      rpow_one_add_le_one_add_mul_self (by linarith : (-1 : ℝ) ≤ x)
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hl : 1 - x / 4 ≤ 1 / (1 + x / 4) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x / 4)).mpr
    nlinarith [sq_nonneg x]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hb.le, Real.one_rpow]
  exact hl.trans (one_div_le_one_div_of_le hy hu)

/-- A sharp tangent bound for every reference atom, with no positive-mass
assumption after multiplication by its mass. -/
theorem reference_allocation_summand_lower {a t h : ℝ} (ha : 0 ≤ a) (hah : a ≤ h) :
    a * (1 - t ^ 2 * h / 4) ≤
      a * (a / (a + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have heq : a / (a + t ^ 2 * a ^ 2) = 1 / (1 + t ^ 2 * a) := by
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ ha
  have hh := mul_le_mul_of_nonneg_left hah (sq_nonneg t)
  exact (by linarith : 1 - t ^ 2 * h / 4 ≤ 1 - (t ^ 2 * a) / 4).trans
    (reciprocal_quarter_rpow_tangent (mul_nonneg (sq_nonneg t) ha))

/-- The manuscript's tangent lower bound, for every countable reference and
every atom cap, proved using the actual allocation `u = q.mass`. -/
theorem allocationD_reference_tangent_lower (q : DiscreteLaw) (t h : ℝ)
    (hcap : ∀ i, q.mass i ≤ h) :
    1 - t ^ 2 * h / 4 ≤ allocationD q.mass t := by
  have hp : ∀ i, q.mass i * (1 - t ^ 2 * h / 4) ≤
      q.mass i * (q.mass i / (q.mass i + t ^ 2 * q.mass i ^ 2)) ^ (1 / 4 : ℝ) :=
    fun i => reference_allocation_summand_lower (q.nonneg i) (hcap i)
  have hs := (q.summable.mul_right (1 - t ^ 2 * h / 4)).tsum_le_tsum hp
    (countableAllocationObjective_summable t q.nonneg q.summable q.nonneg)
  rw [tsum_mul_right, q.total, one_mul] at hs
  exact hs.trans (countableAllocationObjective_le_allocationD t q.nonneg q.summable
    ⟨q.nonneg, q.summable, q.total.le⟩)

theorem allocationD_largestMass_tangent_lower (q : DiscreteLaw) (t : ℝ) :
    1 - t ^ 2 * largestMass q / 4 ≤ allocationD q.mass t := by
  apply allocationD_reference_tangent_lower
  intro i
  rw [largestMass_eq_selected]
  exact largestIndex_spec q i

/-- The quantitative root bound `T² ≥ 4δ/h`, retaining the original root and
radius. This is stronger than the earlier rounding-only estimate. -/
theorem allocationRoot_sq_ge_four_residual_div_largestMass (q : DiscreteLaw)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    4 * (1 - ε) / largestMass q ≤ allocationRoot q ε ^ 2 := by
  have h := allocationD_largestMass_tangent_lower q (allocationRoot q ε)
  rw [(allocationRoot_spec q hε0 hε1).2] at h
  apply (div_le_iff₀ (largestMass_pos q)).mpr
  nlinarith

/-- Exact original `gen:root-rounding`, including its boundary overlap. -/
theorem allocationRoot_sharp_rounding (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hbranch : largestMass q / 2 ≤ 1 - ε) :
    2 ≤ 4 * (1 - ε) / largestMass q ∧
      4 * (1 - ε) / largestMass q ≤ allocationRoot q ε ^ 2 ∧
      Real.sqrt 2 ≤ allocationRoot q ε := by
  have hfrac : (2 : ℝ) ≤ 4 * (1 - ε) / largestMass q := by
    apply (le_div_iff₀ (largestMass_pos q)).mpr
    linarith
  have hs := allocationRoot_sq_ge_four_residual_div_largestMass q hε0 hε1
  refine ⟨hfrac, hs, ?_⟩
  have hT := (allocationRoot_spec q hε0 hε1).1
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem allocationRoot_sharp_sample_rounding (q : DiscreteLaw) {ε K : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hbranch : largestMass q / 2 ≤ 1 - ε)
    (hK : 0 ≤ K) :
    (⌈K * allocationRoot q ε⌉₊ : ℝ) ≤ (K + 1) * allocationRoot q ε := by
  have hT := (allocationRoot_spec q hε0 hε1).1
  have hb := allocationRoot_sharp_rounding q hε0 hε1 hbranch
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hT1 : 1 ≤ allocationRoot q ε := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hc := Nat.ceil_lt_add_one (mul_nonneg hK hT.le)
  nlinarith

theorem allocationD_sqrt_two_lower (q : DiscreteLaw) :
    1 - largestMass q / 2 ≤ allocationD q.mass (Real.sqrt 2) := by
  have h := allocationD_largestMass_tangent_lower q (Real.sqrt 2)
  rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] at h
  linarith

theorem allocationD_global_tangent_lower (q : DiscreteLaw) (t : ℝ) :
    1 - t ^ 2 / 4 ≤ allocationD q.mass t := by
  simpa only [mul_one] using allocationD_reference_tangent_lower q t 1 q.mass_le_one

/-- The strict lower endpoint of `compute:global-initial` is the original
rational residual radius itself. No numerical root approximation is assumed. -/
theorem allocationD_at_residual_gt_radius (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ε < allocationD q.mass (1 - ε) := by
  have h := allocationD_global_tangent_lower q (1 - ε)
  have hd0 : 0 < 1 - ε := sub_pos.mpr hε1
  have hd1 : 1 - ε < 1 := by linarith
  have hsq := mul_lt_mul_of_pos_left hd1 hd0
  nlinarith

theorem residual_lt_allocationRoot (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 - ε < allocationRoot q ε := by
  have hgap := allocationD_at_residual_gt_radius q hε0 hε1
  by_contra hnot
  have hmono := allocationD_antitone q.nonneg q.summable
    (allocationRoot_spec q hε0 hε1).1.le (le_of_not_gt hnot)
  rw [(allocationRoot_spec q hε0 hε1).2] at hmono
  linarith

end IdentityTesting
