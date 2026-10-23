import IdentityTesting.NormalizedTruncationTesting
import IdentityTesting.FiniteTestingRelabeling
import IdentityTesting.MomentLowerBound
import IdentityTesting.HeavyRelabelingLowerBound

/-! Finite lower bounds passed to the original law along normalized truncations.
These proofs use the explicitly constructed 100-batch test and epsilon+2r. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem normalized_allocation_lower (q : DiscreteLaw)
    (hq : largestMass q ≤ 3 / 4) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / (10 : ℝ) ^ 14) * allocationRoot q ε ≤ n := by
  have hlim := (allocationRoot_prefixNormalized_plus_two_tendsto q hε0 hε1).const_mul
    (1 / (10 : ℝ) ^ 12)
  have hle : (1 / (10 : ℝ) ^ 12) * allocationRoot q ε ≤ (100 * n : ℕ) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_normalized_hasIdentityTest q n hε1 htest,
      eventually_normalized_transfer_parameters q n hε1,
      eventually_prefixNormalized_cap_four_fifths q hq] with m ht hm hcap
    have he0 : 0 < ε + 2 * residualMass q (Finset.range m) :=
      add_pos_of_pos_of_nonneg hε0 (mul_nonneg (by norm_num) (tsum_nonneg (fun i => q.nonneg i)))
    have hc : ∀ i, (prefixNormalizedFinite q m).mass i ≤ (4 : ℝ) / 5 := by
      intro i
      exact (show (prefixNormalizedLaw q m).mass i.val ≤ largestMass (prefixNormalizedLaw q m) by
        rw [largestMass_eq_selected]; exact largestIndex_spec _ _).trans hcap
    apply le_of_lt
    apply lt_of_not_ge
    intro hn
    have hno := no_identityTest_of_general_allocation_root_with_zeros
      (prefixNormalizedFinite q m) hc _ he0 hm.2.2 (100 * n)
    rw [extendFiniteLaw_prefixNormalizedFinite] at hno
    exact hno hn ht
  norm_num at hle ⊢
  linarith

theorem normalized_moment_lower (q : DiscreteLaw)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / 100000 : ℝ) * (1 / overlapMoment q (1 - ε)) ≤ n := by
  have hlim := (overlapMoment_reciprocal_prefixNormalized_minus_two_tendsto q
    (sub_pos.mpr hε1)).const_mul (1 / 1000 : ℝ)
  have hle : (1 / 1000 : ℝ) * (1 / overlapMoment q (1 - ε)) ≤ (100 * n : ℕ) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_normalized_hasIdentityTest q n hε1 htest,
      eventually_normalized_transfer_parameters q n hε1] with m ht hm
    have hδ : 0 < 1 - ε - 2 * residualMass q (Finset.range m) := by linarith [hm.2.2]
    apply le_of_lt
    apply lt_of_not_ge
    intro hn
    have hno := no_identityTest_of_overlap_moment (prefixNormalizedFinite q m)
      (1 - ε - 2 * residualMass q (Finset.range m)) hδ (100 * n)
    rw [extendFiniteLaw_prefixNormalizedFinite] at hno
    apply hno (by convert hn using 1 <;> ring)
    convert ht using 1 <;> ring
  norm_num at hle ⊢
  linarith

theorem normalized_heavy_scale_tendsto (q : DiscreteLaw)
    (hinf : (Function.support q.mass).Infinite)
    (hh : 3 / 4 < largestMass q) (hq : largestMass q < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun m => complexityScale (prefixNormalizedLaw q m)
      (ε + 2 * residualMass q (Finset.range m))) atTop (𝓝 (complexityScale q ε)) := by
  have hev := (largestMass_prefixNormalized_tendsto q).eventually (gt_mem_nhds hq)
  have hrad := (normalized_radius_tendsto q ε).eventually (gt_mem_nhds hε1)
  have hheavy := eventually_normalized_heavy q hh
  rcases lt_trichotomy ε (1 - largestMass q) with hi | he | ho
  · have heq : (fun m => complexityScale (prefixNormalizedLaw q m)
        (ε + 2 * residualMass q (Finset.range m))) =ᶠ[atTop]
        (fun m => heavyRoot (prefixNormalizedLaw q m)
          (ε + 2 * residualMass q (Finset.range m))) := by
      filter_upwards [hev, hrad, hheavy, eventually_normalized_interior q hi] with m hm he hh hi
      simp only [complexityScale, ne_of_lt he, ne_of_lt hm, hh, hi.le, if_false, if_true]
    rw [tendsto_congr' heq]
    simpa only [complexityScale, ne_of_lt hε1, ne_of_lt hq, hh, hi.le, if_false, if_true] using
      heavyRoot_prefixNormalized_plus_two_tendsto q hq hε0
  · subst ε
    have heq : (fun m => complexityScale (prefixNormalizedLaw q m)
        (1 - largestMass q + 2 * residualMass q (Finset.range m))) =ᶠ[atTop]
        (fun m => min (heavyRoot (prefixNormalizedLaw q m)
          (1 - largestMass (prefixNormalizedLaw q m)))
          (normalizedExteriorCount q (1 - largestMass q) m)) := by
      filter_upwards [hev, hrad, hheavy, eventually_normalized_boundary_gap_pos q hinf]
        with m hm he hh hg
      have ho : ¬ 1 - largestMass q + 2 * residualMass q (Finset.range m) ≤
          1 - largestMass (prefixNormalizedLaw q m) := by
        unfold normalizedExteriorGap at hg
        linarith
      simp only [complexityScale, ne_of_lt he, ne_of_lt hm, hh, ho, if_false, if_true,
        normalizedExteriorCount, normalizedExteriorGap]
    rw [tendsto_congr' heq]
    simpa only [complexityScale, ne_of_lt hε1, ne_of_lt hq, hh, le_refl, if_false, if_true] using
      normalized_boundary_minimum_tendsto q hq hinf
  · have heq : (fun m => complexityScale (prefixNormalizedLaw q m)
        (ε + 2 * residualMass q (Finset.range m))) =ᶠ[atTop]
        (fun m => min (heavyRoot (prefixNormalizedLaw q m)
          (1 - largestMass (prefixNormalizedLaw q m))) (normalizedExteriorCount q ε m)) := by
      filter_upwards [hev, hrad, hheavy, eventually_normalized_exterior q ho] with m hm he hh ho
      simp only [complexityScale, ne_of_lt he, ne_of_lt hm, hh, not_le.mpr ho, if_false, if_true,
        normalizedExteriorCount, normalizedExteriorGap]
    rw [tendsto_congr' heq]
    simpa only [complexityScale, ne_of_lt hε1, ne_of_lt hq, hh, not_le.mpr ho, if_false, if_true] using
      normalized_exterior_minimum_tendsto q hq ho

theorem normalized_heavy_lower (q : DiscreteLaw)
    (hinf : (Function.support q.mass).Infinite)
    (hh : 3 / 4 < largestMass q) (hq : largestMass q < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / (10 : ℝ) ^ 13) * complexityScale q ε ≤ n := by
  have hlim := (normalized_heavy_scale_tendsto q hinf hh hq hε0 hε1).const_mul
    (1 / (10 : ℝ) ^ 11)
  have hle : (1 / (10 : ℝ) ^ 11) * complexityScale q ε ≤ (100 * n : ℕ) := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_normalized_hasIdentityTest q n hε1 htest,
      eventually_normalized_transfer_parameters q n hε1,
      eventually_normalized_heavy q hh,
      (largestMass_prefixNormalized_tendsto q).eventually (gt_mem_nhds hq)] with m ht hm hh hq
    have he0 : 0 < ε + 2 * residualMass q (Finset.range m) :=
      add_pos_of_pos_of_nonneg hε0 (mul_nonneg (by norm_num) (tsum_nonneg (fun i => q.nonneg i)))
    apply le_of_lt
    apply lt_of_not_ge
    intro hn
    have hno := no_identityTest_of_finite_heavy_complexityScale_with_zeros
      (prefixNormalizedFinite q m)
    simp only [extendFiniteLaw_prefixNormalizedFinite] at hno
    exact hno hh hq he0 hm.2.2 (100 * n) hn ht
  norm_num at hle ⊢
  linarith

end IdentityTesting
