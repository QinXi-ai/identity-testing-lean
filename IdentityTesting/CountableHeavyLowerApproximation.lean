import IdentityTesting.CountableLowerApproximation

/-! The full original heavy scale survives the increased radius required by
reverse pooling, including the exact boundary ε = 1 - largestMass q. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

private theorem eventually_ge_half_of_tendsto {f : ℕ → ℝ} {x : ℝ}
    (hx : 0 < x) (hf : Tendsto f atTop (𝓝 x)) : ∀ᶠ m in atTop, x / 2 ≤ f m :=
  (hf.eventually (lt_mem_nhds (by linarith : x / 2 < x))).mono (fun _ h => h.le)

theorem eventually_heavy_complexityScale_prefixPooled_plus_ge_half (q : DiscreteLaw)
    (hheavy : 3 / 4 < largestMass q) (hq : largestMass q < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ m in atTop, complexityScale q ε / 2 ≤
      complexityScale (prefixPooledLaw q m) (ε + residualMass q (Finset.range m)) := by
  have hεne : ε ≠ 1 := ne_of_lt hε1
  have hqne : largestMass q ≠ 1 := ne_of_lt hq
  have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
  have hradius : ∀ᶠ m in atTop, ε + residualMass q (Finset.range m) < 1 := by
    have hs := (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds (sub_pos.mpr hε1))
    filter_upwards [hs] with m hm
    linarith
  by_cases hin : ε < 1 - largestMass q
  · have hroot := eventually_ge_half_of_tendsto (heavyRoot_pos q hq hε0)
      (heavyRoot_prefixPooled_plus_tendsto q hq hε0)
    have hsmall := (prefixResidual_tendsto_zero q).eventually
      (gt_mem_nhds (sub_pos.mpr hin))
    filter_upwards [eventually_prefixPooled_head q, hradius, hroot, hsmall]
      with m hm he1 hroot hsmall
    have hinm : ε + residualMass q (Finset.range m) ≤ 1 - largestMass q := by linarith
    simpa only [complexityScale, hεne, ne_of_lt he1, hm.2.2.1, hqne, hheavy,
      hin.le, hinm, if_false, if_true] using hroot
  · by_cases heq : ε = 1 - largestMass q
    · subst ε
      have hT : 0 < heavyRoot q (1 - largestMass q) := heavyRoot_pos q hq hR
      have hroot := eventually_ge_half_of_tendsto hT
        (heavyRoot_prefixPooled_tendsto q hq hR)
      have hsmall := (prefixResidual_tendsto_zero q).eventually
        (gt_mem_nhds (one_div_pos.mpr (by linarith : 0 < heavyRoot q (1 - largestMass q) + 1)))
      filter_upwards [eventually_prefixPooled_head q, hradius, hroot, hsmall]
        with m hm he1 hroot hsmall
      have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
      simp only [complexityScale, hεne, ne_of_lt he1, hm.2.2.1, hqne, hheavy,
        le_refl, if_false, if_true]
      split_ifs with hinm
      · have hz : residualMass q (Finset.range m) = 0 := by linarith
        simpa only [hz, add_zero] using hroot
      · apply le_min hroot
        have hrpos : 0 < residualMass q (Finset.range m) := by linarith
        have hprod := (lt_div_iff₀ (by linarith : 0 < heavyRoot q (1 - largestMass q) + 1)).mp hsmall
        have hrecip : heavyRoot q (1 - largestMass q) / 2 ≤
            1 / residualMass q (Finset.range m) := by
          apply (le_div_iff₀ hrpos).mpr
          nlinarith only [hprod, hr, hT]
        have hden : (1 - largestMass q) + residualMass q (Finset.range m) -
            (1 - largestMass q) = residualMass q (Finset.range m) := by ring
        rw [hden]
        exact hrecip.trans (le_add_of_nonneg_left (div_nonneg hR.le (sq_nonneg _)))
    · have hout : 1 - largestMass q < ε := lt_of_le_of_ne (le_of_not_gt hin) (Ne.symm heq)
      have hgap : 0 < ε - (1 - largestMass q) := sub_pos.mpr hout
      have heps : Tendsto
          (fun m => ε + residualMass q (Finset.range m) - (1 - largestMass q)) atTop
          (𝓝 (ε - (1 - largestMass q))) := by
        have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
        simpa only [add_zero] using
          (hc.add (prefixResidual_tendsto_zero q)).sub_const (1 - largestMass q)
      have hratio : Tendsto
          (fun m => (1 - largestMass q) /
              (ε + residualMass q (Finset.range m) - (1 - largestMass q)) ^ 2 +
            1 / (ε + residualMass q (Finset.range m) - (1 - largestMass q))) atTop
          (𝓝 ((1 - largestMass q) / (ε - (1 - largestMass q)) ^ 2 +
            1 / (ε - (1 - largestMass q)))) :=
        (tendsto_const_nhds.div (heps.pow 2) (pow_ne_zero 2 (ne_of_gt hgap))).add
          (tendsto_const_nhds.div heps (ne_of_gt hgap))
      have hconv := (heavyRoot_prefixPooled_tendsto q hq hR).min hratio
      have hpos := lt_min (heavyRoot_pos q hq hR)
        (add_pos (div_pos hR (sq_pos_of_pos hgap)) (one_div_pos.mpr hgap))
      have hhalf := eventually_ge_half_of_tendsto hpos hconv
      filter_upwards [eventually_prefixPooled_head q, hradius, hhalf] with m hm he1 hhalf
      have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
      have houtm : ¬ ε + residualMass q (Finset.range m) ≤ 1 - largestMass q := by linarith
      simpa only [complexityScale, hεne, ne_of_lt he1, hm.2.2.1, hqne, hheavy,
        not_le.mpr hout, houtm, if_false, if_true] using hhalf

end IdentityTesting
