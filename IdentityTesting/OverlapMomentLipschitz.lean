import IdentityTesting.OverlapMoment
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The sharp uniform ℓ¹ bound for the actual overlap-moment summands.
The scalar proof uses square-root algebra, including the junction at δ. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

private theorem moment_three_halves_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- The manuscript's two scalar expressions agree on the original domain. -/
theorem overlapMoment_summand_eq_mul_min {x δ : ℝ} (hx : 0 ≤ x) :
    min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) =
      x * min 1 (Real.sqrt (x / δ)) := by
  rw [moment_three_halves_eq hx, Real.sqrt_div hx, mul_min_of_nonneg _ _ hx]
  simp only [mul_one, mul_div_assoc]

private theorem moment_summand_of_le {x δ : ℝ}
    (hx : 0 ≤ x) (hδ : 0 < δ) (hxδ : x ≤ δ) :
    min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) =
      x * Real.sqrt x / Real.sqrt δ := by
  rw [moment_three_halves_eq hx, min_eq_right]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hδ)).2
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxδ) hx)

private theorem moment_summand_of_ge {x δ : ℝ}
    (hx : 0 ≤ x) (hδ : 0 < δ) (hδx : δ ≤ x) :
    min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) = x := by
  rw [moment_three_halves_eq hx, min_eq_left]
  exact (le_div_iff₀ (Real.sqrt_pos.mpr hδ)).2
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδx) hx)

private theorem moment_summand_low_diff {x y δ : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyδ : y ≤ δ) (hδ : 0 < δ) :
    0 ≤ min y (y ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) ∧
      min y (y ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) ≤ (3 / 2 : ℝ) * (y - x) := by
  have hy := hx.trans hxy
  have ha := Real.sqrt_nonneg x
  have hab := Real.sqrt_le_sqrt hxy
  have hbd := Real.sqrt_le_sqrt hyδ
  have hd := Real.sqrt_pos.mpr hδ
  rw [moment_summand_of_le hy hδ hyδ,
    moment_summand_of_le hx hδ (hxy.trans hyδ), ← sub_div]
  constructor
  · exact div_nonneg (sub_nonneg.mpr (mul_le_mul hxy hab ha hy)) hd.le
  · apply (div_le_iff₀ hd).2
    have hfactor : 0 ≤ (Real.sqrt y - Real.sqrt x) *
        (3 * (Real.sqrt δ - Real.sqrt y) * (Real.sqrt y + Real.sqrt x) +
          (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + 2 * Real.sqrt x)) := by
      have hab0 := sub_nonneg.mpr hab
      have hbd0 := sub_nonneg.mpr hbd
      positivity
    have hid : (Real.sqrt y - Real.sqrt x) *
        (3 * (Real.sqrt δ - Real.sqrt y) * (Real.sqrt y + Real.sqrt x) +
          (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + 2 * Real.sqrt x)) =
        3 * Real.sqrt δ * (y - x) - 2 * (y * Real.sqrt y - x * Real.sqrt x) := by
      calc
        _ = 3 * Real.sqrt δ * ((Real.sqrt y) ^ 2 - (Real.sqrt x) ^ 2) -
            2 * ((Real.sqrt y) ^ 2 * Real.sqrt y -
              (Real.sqrt x) ^ 2 * Real.sqrt x) := by ring
        _ = _ := by rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
    rw [hid] at hfactor
    nlinarith only [hfactor]

private theorem moment_summand_ordered_diff {x y δ : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hδ : 0 < δ) :
    0 ≤ min y (y ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) ∧
      min y (y ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) ≤ (3 / 2 : ℝ) * (y - x) := by
  by_cases hyδ : y ≤ δ
  · exact moment_summand_low_diff hx hxy hyδ hδ
  · have hδy := le_of_not_ge hyδ
    rw [moment_summand_of_ge (hx.trans hxy) hδ hδy]
    by_cases hxδ : x ≤ δ
    · have h := moment_summand_low_diff hx hxδ le_rfl hδ
      rw [moment_summand_of_ge hδ.le hδ le_rfl] at h
      constructor <;> linarith [h.1, h.2]
    · rw [moment_summand_of_ge hx hδ (le_of_not_ge hxδ)]
      constructor <;> linarith

/-- The original min/rpow summand is 3/2-Lipschitz on nonnegative masses. -/
theorem overlapMoment_summand_abs_sub_le {x y δ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 < δ) :
    |min x (x ^ (3 / 2 : ℝ) / Real.sqrt δ) -
      min y (y ^ (3 / 2 : ℝ) / Real.sqrt δ)| ≤ (3 / 2 : ℝ) * |x - y| := by
  rcases le_total x y with hxy | hyx
  · have h := moment_summand_ordered_diff hx hxy hδ
    rw [abs_sub_comm, abs_of_nonneg h.1, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h.2
  · have h := moment_summand_ordered_diff hy hyx hδ
    rw [abs_of_nonneg h.1, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h.2

/-- The exact fδ(x) expression used in the manuscript has the same constant. -/
theorem overlapMoment_mul_min_abs_sub_le {x y δ : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 < δ) :
    |x * min 1 (Real.sqrt (x / δ)) - y * min 1 (Real.sqrt (y / δ))| ≤
      (3 / 2 : ℝ) * |x - y| := by
  simpa only [← overlapMoment_summand_eq_mul_min hx,
    ← overlapMoment_summand_eq_mul_min hy] using
      overlapMoment_summand_abs_sub_le hx hy hδ

/-- No normalization or finite-support hypothesis is needed for summability. -/
theorem overlapMoment_summand_summable {ι : Type*} {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hs : Summable v) (δ : ℝ) :
    Summable (fun i => min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ)) := by
  exact Summable.of_nonneg_of_le
    (fun i => le_min (hv i)
      (div_nonneg (Real.rpow_nonneg (hv i) _) (Real.sqrt_nonneg _)))
    (fun i => min_le_left _ _) hs

/-- The ℓ¹ estimate holds for arbitrary summable nonnegative vectors. -/
theorem overlapMoment_sum_abs_sub_le {ι : Type*} {v w : ι → ℝ} {δ : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (hvs : Summable v) (hws : Summable w) (hδ : 0 < δ) :
    |(∑' i, min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ)) -
      ∑' i, min (w i) (w i ^ (3 / 2 : ℝ) / Real.sqrt δ)| ≤
      (3 / 2 : ℝ) * ∑' i, |v i - w i| := by
  have hvf := overlapMoment_summand_summable hv hvs δ
  have hwf := overlapMoment_summand_summable hw hws δ
  calc
    _ = |∑' i, (min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min (w i) (w i ^ (3 / 2 : ℝ) / Real.sqrt δ))| := by
      rw [hvf.tsum_sub hwf]
    _ ≤ ∑' i, |min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ) -
        min (w i) (w i ^ (3 / 2 : ℝ) / Real.sqrt δ)| := by
      have hnorm : Summable (fun i => ‖min (v i)
          (v i ^ (3 / 2 : ℝ) / Real.sqrt δ) -
          min (w i) (w i ^ (3 / 2 : ℝ) / Real.sqrt δ)‖) := by
        simpa only [Real.norm_eq_abs] using (hvf.sub hwf).abs
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, (3 / 2 : ℝ) * |v i - w i| :=
      (hvf.sub hwf).abs.tsum_le_tsum
        (fun i => overlapMoment_summand_abs_sub_le (hv i) (hw i) hδ)
        ((hvs.sub hws).abs.mul_left _)
    _ = _ := tsum_mul_left

/-- The vector estimate specializes to the existing original `overlapMoment`. -/
theorem overlapMoment_abs_sub_le_l1 (p q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    |overlapMoment p δ - overlapMoment q δ| ≤
      (3 / 2 : ℝ) * ∑' i, |p.mass i - q.mass i| :=
  overlapMoment_sum_abs_sub_le p.nonneg q.nonneg p.summable q.summable hδ

theorem overlapMoment_abs_sub_le_totalVariation (p q : DiscreteLaw)
    {δ : ℝ} (hδ : 0 < δ) :
    |overlapMoment p δ - overlapMoment q δ| ≤ 3 * totalVariation p q := by
  have h := overlapMoment_abs_sub_le_l1 p q hδ
  unfold totalVariation
  linarith

end IdentityTesting
