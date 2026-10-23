import IdentityTesting.CountableFiniteApproximation
import IdentityTesting.OverlapMoment
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual overlap-moment approximation for finite pooled references, including
the perturbed overlap target δ plus the residual mass. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IdentityTesting

theorem overlapMoment_prefix_bounds (q : DiscreteLaw) (s : Finset ℕ) (δ : ℝ) :
    (∑ i ∈ s, min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)) ≤ overlapMoment q δ ∧
    overlapMoment q δ ≤
      (∑ i ∈ s, min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)) +
        discardedMass q.mass s := by
  have hs := overlapMoment_summable q δ
  have hnonneg (i : ℕ) : 0 ≤ min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ) :=
    le_min (q.nonneg i)
      (div_nonneg (Real.rpow_nonneg (q.nonneg i) _) (Real.sqrt_nonneg _))
  constructor
  · exact hs.sum_le_tsum s (fun i _ => hnonneg i)
  · have hsplit := hs.sum_add_tsum_compl (s := s)
    have htail : (∑' i : {i : ℕ // i ∉ s},
        min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)) ≤ discardedMass q.mass s :=
      (hs.subtype {i | i ∉ s}).tsum_le_tsum (fun i => min_le_left _ _)
        (q.summable.subtype {i | i ∉ s})
    exact hsplit.symm.le.trans (add_le_add_left htail _)

theorem overlapMoment_prefixPooled_abs_le (q : DiscreteLaw) (m : ℕ) (δ : ℝ) :
    |overlapMoment (prefixPooledLaw q m) δ - overlapMoment q δ| ≤
      residualMass q (Finset.range m) := by
  have hp := overlapMoment_prefix_bounds (prefixPooledLaw q m) (Finset.range m) δ
  have hq := overlapMoment_prefix_bounds q (Finset.range m) δ
  have heq :
      (∑ i ∈ Finset.range m, min ((prefixPooledLaw q m).mass i)
        ((prefixPooledLaw q m).mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)) =
      ∑ i ∈ Finset.range m, min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp hi)]
  rw [heq, prefixPooledLaw_discardedMass] at hp
  change _ ≤ overlapMoment q δ ∧ overlapMoment q δ ≤
    _ + residualMass q (Finset.range m) at hq
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

theorem continuousOn_overlapMoment (q : DiscreteLaw) :
    ContinuousOn (overlapMoment q) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun δ : {δ : ℝ // 0 < δ} =>
    ∑' i, min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ.val))
  apply continuous_tsum (u := q.mass) _ q.summable _
  · intro i
    apply continuous_const.min
    exact continuous_const.div continuous_subtype_val.sqrt
      (fun δ => ne_of_gt (Real.sqrt_pos.mpr δ.property))
  · intro i δ
    have h0 : 0 ≤ min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ.val) :=
      le_min (q.nonneg i)
        (div_nonneg (Real.rpow_nonneg (q.nonneg i) _) (Real.sqrt_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _

/-- Any convergent positive-limit overlap targets, with actual coarsened laws. -/
theorem overlapMoment_prefixPooled_tendsto_targets (q : DiscreteLaw)
    {δm : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hm : Tendsto δm atTop (𝓝 δ)) :
    Tendsto (fun m => overlapMoment (prefixPooledLaw q m) (δm m)) atTop
      (𝓝 (overlapMoment q δ)) := by
  have hc : ContinuousAt (overlapMoment q) δ :=
    (continuousOn_overlapMoment q).continuousAt (isOpen_Ioi.mem_nhds hδ)
  have hfixed := hc.tendsto.comp hm
  have habs : Tendsto (fun m =>
      |overlapMoment (prefixPooledLaw q m) (δm m) - overlapMoment q (δm m)|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun m => overlapMoment_prefixPooled_abs_le q m (δm m)) (prefixResidual_tendsto_zero q)
  have hdiff : Tendsto (fun m =>
      overlapMoment (prefixPooledLaw q m) (δm m) - overlapMoment q (δm m)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (by simpa only [sub_zero, Real.norm_eq_abs] using habs)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hdiff.add hfixed

theorem overlapMoment_prefixPooled_shifted_tendsto (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m => overlapMoment (prefixPooledLaw q m)
      (δ + residualMass q (Finset.range m))) atTop (𝓝 (overlapMoment q δ)) := by
  apply overlapMoment_prefixPooled_tendsto_targets q hδ
  have hc : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
  simpa only [add_zero] using hc.add (prefixResidual_tendsto_zero q)

theorem overlapMoment_reciprocal_prefixPooled_tendsto (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m => 1 / overlapMoment (prefixPooledLaw q m)
      (δ + residualMass q (Finset.range m))) atTop (𝓝 (1 / overlapMoment q δ)) := by
  exact tendsto_const_nhds.div (overlapMoment_prefixPooled_shifted_tendsto q hδ)
    (ne_of_gt (overlapMoment_pos q hδ))

end IdentityTesting
