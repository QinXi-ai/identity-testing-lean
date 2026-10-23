import IdentityTesting.CountableScaleApproximation

/-! Concrete rounded-scale bounds for selecting a finite coarsening in an
actual countable upper-bound proof. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem complexityScale_pos (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < complexityScale q ε := by
  have hεne : ε ≠ 1 := ne_of_lt hε1
  unfold complexityScale
  simp only [hεne, if_false]
  split_ifs with hpoint hheavy hin hin
  · exact one_div_pos.mpr hε0
  · exact heavyRoot_pos q (lt_of_le_of_ne (largestMass_le_one q) hpoint) hε0
  · have hq : largestMass q < 1 := lt_of_le_of_ne (largestMass_le_one q) hpoint
    have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
    have hgap : 0 < ε - (1 - largestMass q) := sub_pos.mpr (lt_of_not_ge hin)
    exact lt_min (heavyRoot_pos q hq hR)
      (add_pos (div_pos hR (sq_pos_of_pos hgap)) (one_div_pos.mpr hgap))
  · exact (allocationRoot_spec q hε0 hε1).1
  · exact one_div_pos.mpr (overlapMoment_pos q (sub_pos.mpr hε1))

theorem eventually_complexityScale_prefixPooled_le_twice (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ m in atTop, complexityScale (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m)) ≤ 2 * complexityScale q ε := by
  have hpos := complexityScale_pos q hε0 hε1
  have hlt : complexityScale q ε < 2 * complexityScale q ε := by linarith
  exact ((complexityScale_prefixPooled_shifted_tendsto q hq hε0 hε1).eventually
    (gt_mem_nhds hlt)).mono (fun _ h => h.le)

theorem eventually_prefixPooled_radius_and_roundedScale (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ m in atTop,
      0 < ε - residualMass q (Finset.range m) ∧
      ε - residualMass q (Finset.range m) < 1 ∧
      roundedScale (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) ≤
        2 * roundedScale q ε := by
  have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < ε :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hε0)
  filter_upwards [hsmall, eventually_complexityScale_prefixPooled_le_twice q hq hε0 hε1]
    with m hsmall hscale
  refine ⟨sub_pos.mpr hsmall, prefixPooled_shifted_radius_lt_one q hε1 m, ?_⟩
  apply Nat.ceil_le.mpr
  have hceil : complexityScale q ε ≤ (roundedScale q ε : ℝ) := Nat.le_ceil _
  exact hscale.trans (by exact_mod_cast mul_le_mul_of_nonneg_left hceil (by norm_num : (0 : ℝ) ≤ 2))

end IdentityTesting
