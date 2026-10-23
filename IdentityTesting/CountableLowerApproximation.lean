import IdentityTesting.CountableScaleBounds

/-! The increased radii needed for the reverse statistical transfer. These
lemmas concern actual roots/moments, without assuming a limit interface. -/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

theorem allocationRoot_prefixPooled_tendsto_targets (q : DiscreteLaw)
    {em : ℕ → ℝ} {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hem : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => allocationRoot (prefixPooledLaw q m) (em m)) atTop
      (𝓝 (allocationRoot q e)) := by
  have hspec := allocationRoot_spec q he0 he1
  apply tendsto_positive_roots (f := allocationD q.mass)
    (fm := fun m => allocationD (prefixPooledLaw q m).mass)
    (em := em) hspec.1 hspec.2
    (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive)
  · intro m t ht r hr htr
    exact allocationD_antitone (prefixPooledLaw q m).nonneg
      (prefixPooledLaw q m).summable ht.le htr
  · intro t _
    exact allocationD_prefixPooled_tendsto q t
  · exact hem
  · have hpositive : ∀ᶠ m in atTop, 0 < em m := hem.eventually (lt_mem_nhds he0)
    have hsmall : ∀ᶠ m in atTop, em m < 1 := hem.eventually (gt_mem_nhds he1)
    filter_upwards [hpositive, hsmall] with m h0 h1
    exact allocationRoot_spec _ h0 h1

theorem allocationRoot_prefixPooled_plus_tendsto (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun m => allocationRoot (prefixPooledLaw q m)
      (ε + residualMass q (Finset.range m))) atTop (𝓝 (allocationRoot q ε)) := by
  apply allocationRoot_prefixPooled_tendsto_targets q hε0 hε1
  have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
  simpa only [add_zero] using hc.add (prefixResidual_tendsto_zero q)

theorem eventually_allocationRoot_prefixPooled_plus_ge_half (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ m in atTop, allocationRoot q ε / 2 ≤ allocationRoot (prefixPooledLaw q m)
      (ε + residualMass q (Finset.range m)) := by
  have hp := (allocationRoot_spec q hε0 hε1).1
  exact ((allocationRoot_prefixPooled_plus_tendsto q hε0 hε1).eventually
    (lt_mem_nhds (by linarith : allocationRoot q ε / 2 < allocationRoot q ε))).mono
      (fun _ h => h.le)

theorem heavyRoot_prefixPooled_plus_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => heavyRoot (prefixPooledLaw q m)
      (ε + residualMass q (Finset.range m))) atTop (𝓝 (heavyRoot q ε)) := by
  apply heavyRoot_prefixPooled_tendsto_targets q hq hε
  have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
  simpa only [add_zero] using hc.add (prefixResidual_tendsto_zero q)

theorem overlapMoment_reciprocal_prefixPooled_minus_tendsto (q : DiscreteLaw)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m => 1 / overlapMoment (prefixPooledLaw q m)
      (δ - residualMass q (Finset.range m))) atTop (𝓝 (1 / overlapMoment q δ)) := by
  apply tendsto_const_nhds.div _ (ne_of_gt (overlapMoment_pos q hδ))
  apply overlapMoment_prefixPooled_tendsto_targets q hδ
  have hc : Tendsto (fun _ : ℕ => δ) atTop (𝓝 δ) := tendsto_const_nhds
  simpa only [sub_zero] using hc.sub (prefixResidual_tendsto_zero q)

theorem eventually_overlapMoment_reciprocal_prefixPooled_minus_ge_half
    (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, (1 / overlapMoment q δ) / 2 ≤
      1 / overlapMoment (prefixPooledLaw q m) (δ - residualMass q (Finset.range m)) := by
  have hp : 0 < 1 / overlapMoment q δ := one_div_pos.mpr (overlapMoment_pos q hδ)
  exact ((overlapMoment_reciprocal_prefixPooled_minus_tendsto q hδ).eventually
    (lt_mem_nhds (by linarith : (1 / overlapMoment q δ) / 2 < 1 / overlapMoment q δ))).mono
      (fun _ h => h.le)

end IdentityTesting
