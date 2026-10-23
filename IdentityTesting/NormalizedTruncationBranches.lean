import IdentityTesting.NormalizedTruncationLimits
import Mathlib.Topology.Algebra.Order.Field

/-! The original epsilon + 2r branch transitions, including the heavy boundary. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IdentityTesting

theorem prefixResidual_pos_of_infinite_support (q : DiscreteLaw)
    (hq : (Function.support q.mass).Infinite) (m : ℕ) :
    0 < residualMass q (Finset.range m) := by
  obtain ⟨i, hi, him⟩ := hq.exists_notMem_finset (Finset.range m)
  have hp : 0 < q.mass i := lt_of_le_of_ne (q.nonneg i) (Ne.symm hi)
  exact hp.trans_le ((q.summable.subtype {i | i ∉ Finset.range m}).le_tsum
    ⟨i, him⟩ (fun i _ => q.nonneg i))

theorem eventually_normalized_heavy (q : DiscreteLaw) (hq : 3 / 4 < largestMass q) :
    ∀ᶠ m in atTop, 3 / 4 < largestMass (prefixNormalizedLaw q m) :=
  (largestMass_prefixNormalized_tendsto q).eventually (lt_mem_nhds hq)

theorem eventually_normalized_interior (q : DiscreteLaw) {ε : ℝ}
    (hε : ε < 1 - largestMass q) :
    ∀ᶠ m in atTop, ε + 2 * residualMass q (Finset.range m) <
      1 - largestMass (prefixNormalizedLaw q m) :=
  (normalized_radius_tendsto q ε).eventually_lt (normalized_tail_mass_tendsto q) hε

theorem eventually_normalized_exterior (q : DiscreteLaw) {ε : ℝ}
    (hε : 1 - largestMass q < ε) :
    ∀ᶠ m in atTop, 1 - largestMass (prefixNormalizedLaw q m) <
      ε + 2 * residualMass q (Finset.range m) :=
  (normalized_tail_mass_tendsto q).eventually_lt (normalized_radius_tendsto q ε) hε

def normalizedExteriorGap (q : DiscreteLaw) (ε : ℝ) (m : ℕ) : ℝ :=
  ε + 2 * residualMass q (Finset.range m) - (1 - largestMass (prefixNormalizedLaw q m))

def normalizedExteriorCount (q : DiscreteLaw) (ε : ℝ) (m : ℕ) : ℝ :=
  (1 - largestMass (prefixNormalizedLaw q m)) / normalizedExteriorGap q ε m ^ 2 +
    1 / normalizedExteriorGap q ε m

theorem normalizedExteriorGap_tendsto (q : DiscreteLaw) (ε : ℝ) :
    Tendsto (normalizedExteriorGap q ε) atTop (𝓝 (ε - (1 - largestMass q))) :=
  (normalized_radius_tendsto q ε).sub (normalized_tail_mass_tendsto q)

theorem normalizedExteriorCount_tendsto (q : DiscreteLaw) {ε : ℝ}
    (hε : 1 - largestMass q < ε) :
    Tendsto (normalizedExteriorCount q ε) atTop
      (𝓝 ((1 - largestMass q) / (ε - (1 - largestMass q)) ^ 2 +
        1 / (ε - (1 - largestMass q)))) :=
  ((normalized_tail_mass_tendsto q).div ((normalizedExteriorGap_tendsto q ε).pow 2)
    (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hε)))).add
      (tendsto_const_nhds.div (normalizedExteriorGap_tendsto q ε) (ne_of_gt (sub_pos.mpr hε)))

theorem normalized_exterior_minimum_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 1 - largestMass q < ε) :
    Tendsto (fun m => min (heavyRoot (prefixNormalizedLaw q m)
      (1 - largestMass (prefixNormalizedLaw q m))) (normalizedExteriorCount q ε m)) atTop
      (𝓝 (min (heavyRoot q (1 - largestMass q))
        ((1 - largestMass q) / (ε - (1 - largestMass q)) ^ 2 +
          1 / (ε - (1 - largestMass q))))) :=
  (heavyRoot_prefixNormalized_boundary_tendsto q hq).min (normalizedExteriorCount_tendsto q hε)

/-- Literal heavy-boundary identity in 05_countable, with no asymptotic surrogate. -/
theorem normalized_boundary_gap_formula (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) < 1) :
    normalizedExteriorGap q (1 - largestMass q) m =
      2 * residualMass q (Finset.range m) +
        largestMass q * residualMass q (Finset.range m) /
          (1 - residualMass q (Finset.range m)) := by
  unfold normalizedExteriorGap
  rw [largestMass_prefixNormalized_eq q m hm hr]
  have hden : 1 - residualMass q (Finset.range m) ≠ 0 := by linarith
  field_simp [hden]
  <;> ring

theorem eventually_normalized_boundary_gap_pos (q : DiscreteLaw)
    (hq : (Function.support q.mass).Infinite) :
    ∀ᶠ m in atTop, 0 < normalizedExteriorGap q (1 - largestMass q) m := by
  filter_upwards [eventually_gt_atTop (largestIndex q), eventually_prefix_residual_lt_one q]
    with m hm hr
  rw [normalized_boundary_gap_formula q m hm hr]
  have hp := prefixResidual_pos_of_infinite_support q hq m
  exact add_pos (by positivity) (div_pos (mul_pos (largestMass_pos q) hp) (by linarith))

/-- At epsilon=R the count expression diverges to infinity for infinite support. -/
theorem normalized_boundary_count_tendsto_atTop (q : DiscreteLaw)
    (hq : (Function.support q.mass).Infinite) :
    Tendsto (normalizedExteriorCount q (1 - largestMass q)) atTop atTop := by
  have hzero : Tendsto (normalizedExteriorGap q (1 - largestMass q)) atTop (𝓝 0) := by
    simpa using normalizedExteriorGap_tendsto q (1 - largestMass q)
  have hright : Tendsto (normalizedExteriorGap q (1 - largestMass q)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, eventually_normalized_boundary_gap_pos q hq⟩
  have hinv : Tendsto (fun m => 1 / normalizedExteriorGap q (1 - largestMass q) m)
      atTop atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero.comp hright
  apply tendsto_atTop_mono _ hinv
  intro m
  unfold normalizedExteriorCount
  exact le_add_of_nonneg_left (div_nonneg
    (sub_nonneg.mpr (largestMass_le_one _)) (sq_nonneg _))

/-- The exterior minimum at the exact original boundary tends to B(R). -/
theorem normalized_boundary_minimum_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) (hinf : (Function.support q.mass).Infinite) :
    Tendsto (fun m => min (heavyRoot (prefixNormalizedLaw q m)
      (1 - largestMass (prefixNormalizedLaw q m)))
        (normalizedExteriorCount q (1 - largestMass q) m)) atTop
      (𝓝 (heavyRoot q (1 - largestMass q))) := by
  have hroot := heavyRoot_prefixNormalized_boundary_tendsto q hq
  have hcount := normalized_boundary_count_tendsto_atTop q hinf
  have hb := hroot.eventually (gt_mem_nhds
    (show heavyRoot q (1 - largestMass q) < heavyRoot q (1 - largestMass q) + 1 by linarith))
  have hc := (tendsto_atTop.1 hcount) (heavyRoot q (1 - largestMass q) + 1)
  apply hroot.congr'
  filter_upwards [hb, hc] with m hm hc
  exact (min_eq_left (hm.le.trans hc)).symm

end IdentityTesting
