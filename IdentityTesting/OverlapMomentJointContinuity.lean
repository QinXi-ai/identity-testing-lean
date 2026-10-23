import IdentityTesting.OverlapMomentLipschitz
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! General ℓ¹ / positive-target joint continuity from count:continuity.
The sequence may have arbitrary support and arbitrary nonnegative summable mass.
The probability-law corollary uses the project's original `overlapMoment`. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IdentityTesting

/-- Dominated continuity in the overlap parameter for an arbitrary mass vector. -/
theorem continuousOn_overlapMoment_sum {ι : Type*} {v : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hs : Summable v) :
    ContinuousOn (fun δ : ℝ => ∑' i,
      min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ)) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun δ : {δ : ℝ // 0 < δ} =>
    ∑' i, min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ.val))
  apply continuous_tsum (u := v) _ hs _
  · intro i
    apply continuous_const.min
    exact continuous_const.div continuous_subtype_val.sqrt
      (fun δ => ne_of_gt (Real.sqrt_pos.mpr δ.property))
  · intro i δ
    have h0 : 0 ≤ min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ.val) :=
      le_min (hv i)
        (div_nonneg (Real.rpow_nonneg (hv i) _) (Real.sqrt_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _

/-- Joint continuity for every ℓ¹-convergent sequence of nonnegative summable
vectors. Only the limiting overlap target must be positive. -/
theorem overlapMoment_sum_tendsto_l1_targets {ι : Type*}
    (vm : ℕ → ι → ℝ) (v : ι → ℝ)
    (hvm : ∀ m i, 0 ≤ vm m i) (hv : ∀ i, 0 ≤ v i)
    (hvms : ∀ m, Summable (vm m)) (hvs : Summable v)
    (hl1 : Tendsto (fun m => ∑' i, |vm m i - v i|) atTop (𝓝 0))
    {δm : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hm : Tendsto δm atTop (𝓝 δ)) :
    Tendsto (fun m => ∑' i, min (vm m i)
      (vm m i ^ (3 / 2 : ℝ) / Real.sqrt (δm m))) atTop
      (𝓝 (∑' i, min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ))) := by
  have hc : ContinuousAt (fun δ : ℝ => ∑' i,
      min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt δ)) δ :=
    (continuousOn_overlapMoment_sum hv hvs).continuousAt (isOpen_Ioi.mem_nhds hδ)
  have hfixed := hc.tendsto.comp hm
  have hpos : ∀ᶠ m in atTop, 0 < δm m := hm.eventually (Ioi_mem_nhds hδ)
  have hbound : Tendsto (fun m => (3 / 2 : ℝ) * ∑' i, |vm m i - v i|)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hl1
  have habs : Tendsto (fun m =>
      |(∑' i, min (vm m i) (vm m i ^ (3 / 2 : ℝ) / Real.sqrt (δm m))) -
        ∑' i, min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt (δm m))|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hbound
    exact hpos.mono (fun m hδm =>
      overlapMoment_sum_abs_sub_le (hvm m) hv (hvms m) hvs hδm)
  have hdiff : Tendsto (fun m =>
      (∑' i, min (vm m i) (vm m i ^ (3 / 2 : ℝ) / Real.sqrt (δm m))) -
        ∑' i, min (v i) (v i ^ (3 / 2 : ℝ) / Real.sqrt (δm m)))
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (by simpa only [sub_zero, Real.norm_eq_abs] using habs)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hdiff.add hfixed

/-- The full probability-law assertion of manuscript count:continuity.
There is no prefix, pooling, finite support, or positivity-of-every-atom premise. -/
theorem overlapMoment_tendsto_l1_targets (qm : ℕ → DiscreteLaw) (q : DiscreteLaw)
    (hl1 : Tendsto (fun m => ∑' i, |(qm m).mass i - q.mass i|) atTop (𝓝 0))
    {δm : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hm : Tendsto δm atTop (𝓝 δ)) :
    Tendsto (fun m => overlapMoment (qm m) (δm m)) atTop
      (𝓝 (overlapMoment q δ)) :=
  overlapMoment_sum_tendsto_l1_targets (fun m => (qm m).mass) q.mass
    (fun m => (qm m).nonneg) q.nonneg (fun m => (qm m).summable) q.summable hl1 hδ hm

theorem overlapMoment_tendsto_totalVariation_targets
    (qm : ℕ → DiscreteLaw) (q : DiscreteLaw)
    (htv : Tendsto (fun m => totalVariation (qm m) q) atTop (𝓝 0))
    {δm : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hm : Tendsto δm atTop (𝓝 δ)) :
    Tendsto (fun m => overlapMoment (qm m) (δm m)) atTop
      (𝓝 (overlapMoment q δ)) := by
  apply overlapMoment_tendsto_l1_targets qm q _ hδ hm
  have h := htv.const_mul (2 : ℝ)
  simpa only [totalVariation, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
    mul_zero] using h

theorem overlapMoment_reciprocal_tendsto_l1_targets
    (qm : ℕ → DiscreteLaw) (q : DiscreteLaw)
    (hl1 : Tendsto (fun m => ∑' i, |(qm m).mass i - q.mass i|) atTop (𝓝 0))
    {δm : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hm : Tendsto δm atTop (𝓝 δ)) :
    Tendsto (fun m => 1 / overlapMoment (qm m) (δm m)) atTop
      (𝓝 (1 / overlapMoment q δ)) :=
  tendsto_const_nhds.div (overlapMoment_tendsto_l1_targets qm q hl1 hδ hm)
    (ne_of_gt (overlapMoment_pos q hδ))

end IdentityTesting
