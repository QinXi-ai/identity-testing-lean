import IdentityTesting.CountableHeavyApproximation
import IdentityTesting.CountableMomentApproximation

/-! The manuscript's entire nondegenerate complexity scale is the limit of
the scales of actual finite coarsenings at the surviving strict radius. -/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

theorem prefixPooled_shifted_radius_lt_one (q : DiscreteLaw) {ε : ℝ}
    (hε : ε < 1) (m : ℕ) : ε - residualMass q (Finset.range m) < 1 := by
  have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
  exact (sub_le_self ε hr).trans_lt hε

theorem complexityScale_prefixPooled_shifted_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun m => complexityScale (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m))) atTop (𝓝 (complexityScale q ε)) := by
  have hεne : ε ≠ 1 := ne_of_lt hε1
  have hqne : largestMass q ≠ 1 := ne_of_lt hq
  have hmne (m : ℕ) : ε - residualMass q (Finset.range m) ≠ 1 :=
    ne_of_lt (prefixPooled_shifted_radius_lt_one q hε1 m)
  by_cases hheavy : 3 / 4 < largestMass q
  · by_cases hin : ε ≤ 1 - largestMass q
    · have heq : (fun m => complexityScale (prefixPooledLaw q m)
          (ε - residualMass q (Finset.range m))) =ᶠ[atTop]
          (fun m => heavyRoot (prefixPooledLaw q m)
            (ε - residualMass q (Finset.range m))) := by
        filter_upwards [eventually_prefixPooled_head q] with m hm
        have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
        have hinm : ε - residualMass q (Finset.range m) ≤ 1 - largestMass q :=
          (sub_le_self ε hr).trans hin
        simp only [complexityScale, hmne m, hm.2.2.1, hqne, hheavy, hinm,
          if_false, if_true]
      rw [tendsto_congr' heq]
      simpa only [complexityScale, hεne, hqne, hheavy, hin, if_false, if_true] using
        heavyRoot_prefixPooled_shifted_tendsto q hq hε0
    · have hgap : 0 < ε - (1 - largestMass q) := sub_pos.mpr (lt_of_not_ge hin)
      have hsmall : ∀ᶠ m in atTop,
          residualMass q (Finset.range m) < ε - (1 - largestMass q) :=
        (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hgap)
      have heq : (fun m => complexityScale (prefixPooledLaw q m)
          (ε - residualMass q (Finset.range m))) =ᶠ[atTop]
          (fun m => min (heavyRoot (prefixPooledLaw q m) (1 - largestMass q))
            ((1 - largestMass q) /
                (ε - residualMass q (Finset.range m) - (1 - largestMass q)) ^ 2 +
              1 / (ε - residualMass q (Finset.range m) - (1 - largestMass q)))) := by
        filter_upwards [eventually_prefixPooled_head q, hsmall] with m hm hsmall
        have houtm : ¬ ε - residualMass q (Finset.range m) ≤ 1 - largestMass q := by
          linarith
        simp only [complexityScale, hmne m, hm.2.2.1, hqne, hheavy, houtm,
          if_false, if_true]
      have heps : Tendsto
          (fun m => ε - residualMass q (Finset.range m) - (1 - largestMass q)) atTop
          (𝓝 (ε - (1 - largestMass q))) := by
        have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
        simpa only [sub_zero] using
          (hc.sub (prefixResidual_tendsto_zero q)).sub_const (1 - largestMass q)
      have hratio : Tendsto
          (fun m => (1 - largestMass q) /
                (ε - residualMass q (Finset.range m) - (1 - largestMass q)) ^ 2 +
              1 / (ε - residualMass q (Finset.range m) - (1 - largestMass q))) atTop
          (𝓝 ((1 - largestMass q) / (ε - (1 - largestMass q)) ^ 2 +
            1 / (ε - (1 - largestMass q)))) :=
        (tendsto_const_nhds.div (heps.pow 2) (pow_ne_zero 2 (ne_of_gt hgap))).add
          (tendsto_const_nhds.div heps (ne_of_gt hgap))
      rw [tendsto_congr' heq]
      simpa only [complexityScale, hεne, hqne, hheavy, hin, if_false, if_true] using
        (heavyRoot_prefixPooled_tendsto q hq (sub_pos.mpr hq)).min hratio
  · by_cases hin : largestMass q / 2 ≤ 1 - ε
    · have heq : (fun m => complexityScale (prefixPooledLaw q m)
          (ε - residualMass q (Finset.range m))) =ᶠ[atTop]
          (fun m => allocationRoot (prefixPooledLaw q m)
            (ε - residualMass q (Finset.range m))) := by
        filter_upwards [eventually_prefixPooled_head q] with m hm
        have hinm : largestMass q / 2 ≤ 1 - (ε - residualMass q (Finset.range m)) := by
          have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
          linarith
        simp only [complexityScale, hmne m, hm.2.2.1, hqne, hheavy, hinm,
          if_false, if_true]
      rw [tendsto_congr' heq]
      simpa only [complexityScale, hεne, hqne, hheavy, hin, if_false, if_true] using
        allocationRoot_prefixPooled_tendsto q hε0 hε1
    · have hgap : 0 < largestMass q / 2 - (1 - ε) := sub_pos.mpr (lt_of_not_ge hin)
      have hsmall : ∀ᶠ m in atTop,
          residualMass q (Finset.range m) < largestMass q / 2 - (1 - ε) :=
        (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hgap)
      have heq : (fun m => complexityScale (prefixPooledLaw q m)
          (ε - residualMass q (Finset.range m))) =ᶠ[atTop]
          (fun m => 1 / overlapMoment (prefixPooledLaw q m)
            ((1 - ε) + residualMass q (Finset.range m))) := by
        filter_upwards [eventually_prefixPooled_head q, hsmall] with m hm hsmall
        have houtm : ¬ largestMass q / 2 ≤ 1 - (ε - residualMass q (Finset.range m)) := by
          linarith
        have hepsm : 1 - (ε - residualMass q (Finset.range m)) =
            (1 - ε) + residualMass q (Finset.range m) := by ring
        simp only [complexityScale, hmne m, hm.2.2.1, hqne, hheavy, houtm, if_false]
        rw [hepsm]
      rw [tendsto_congr' heq]
      simpa only [complexityScale, hεne, hqne, hheavy, hin, if_false, if_true] using
        overlapMoment_reciprocal_prefixPooled_tendsto q (sub_pos.mpr hε1)

end IdentityTesting
