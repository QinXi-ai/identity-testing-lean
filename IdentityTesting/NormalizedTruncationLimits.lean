import IdentityTesting.NormalizedTruncation
import IdentityTesting.CountableHeavyApproximation
import IdentityTesting.OverlapMomentJointContinuity

/-! Root and moment limits for the literal normalized finite truncations.
All limits concern the original allocation and selected largest-atom definitions. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IdentityTesting

theorem normalized_radius_tendsto (q : DiscreteLaw) (ε : ℝ) :
    Tendsto (fun m => ε + 2 * residualMass q (Finset.range m)) atTop (𝓝 ε) := by
  simpa using tendsto_const_nhds.add ((prefixResidual_tendsto_zero q).const_mul 2)

theorem allocationRoot_prefixNormalized_tendsto_targets (q : DiscreteLaw)
    {em : ℕ → ℝ} {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (hem : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => allocationRoot (prefixNormalizedLaw q m) (em m)) atTop
      (𝓝 (allocationRoot q e)) := by
  have hspec := allocationRoot_spec q he0 he1
  apply tendsto_positive_roots (f := allocationD q.mass)
    (fm := fun m => allocationD (prefixNormalizedLaw q m).mass)
    (em := em) hspec.1 hspec.2
    (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive)
  · intro m t ht r hr htr
    exact allocationD_antitone (prefixNormalizedLaw q m).nonneg
      (prefixNormalizedLaw q m).summable ht.le htr
  · exact fun t _ => allocationD_prefixNormalized_tendsto q t
  · exact hem
  · filter_upwards [hem.eventually (lt_mem_nhds he0), hem.eventually (gt_mem_nhds he1)]
      with m h0 h1
    exact allocationRoot_spec _ h0 h1

theorem allocationRoot_prefixNormalized_plus_two_tendsto (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun m => allocationRoot (prefixNormalizedLaw q m)
      (ε + 2 * residualMass q (Finset.range m))) atTop (𝓝 (allocationRoot q ε)) :=
  allocationRoot_prefixNormalized_tendsto_targets q hε0 hε1 (normalized_radius_tendsto q ε)

theorem overlapMoment_reciprocal_prefixNormalized_minus_two_tendsto
    (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m => 1 / overlapMoment (prefixNormalizedLaw q m)
      (δ - 2 * residualMass q (Finset.range m))) atTop (𝓝 (1 / overlapMoment q δ)) := by
  apply overlapMoment_reciprocal_tendsto_l1_targets _ q
    (prefixNormalized_l1_tendsto_zero q) hδ
  simpa using tendsto_const_nhds.sub ((prefixResidual_tendsto_zero q).const_mul 2)

theorem largestMass_prefixNormalized_eq (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) < 1) :
    largestMass (prefixNormalizedLaw q m) =
      largestMass q / (1 - residualMass q (Finset.range m)) := by
  have hden : 0 < 1 - residualMass q (Finset.range m) := by linarith
  have hbound : ∀ i, (prefixNormalizedLaw q m).mass i ≤
      largestMass q / (1 - residualMass q (Finset.range m)) := by
    intro i
    rw [prefixNormalizedLaw_mass q m i hr]
    split_ifs
    · apply div_le_div_of_nonneg_right _ hden.le
      rw [largestMass_eq_selected]
      exact largestIndex_spec q i
    · exact div_nonneg (largestMass_pos q).le hden.le
  apply le_antisymm
  · rw [largestMass_eq_selected]
    exact hbound _
  · rw [largestMass_eq_selected q]
    have h := largestIndex_spec (prefixNormalizedLaw q m) (largestIndex q)
    rw [prefixNormalizedLaw_mass q m _ hr, if_pos hm,
      ← largestMass_eq_selected (prefixNormalizedLaw q m)] at h
    exact h

theorem largestIndex_prefixNormalized_eq (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) < 1) :
    largestIndex (prefixNormalizedLaw q m) = largestIndex q := by
  have hmass := largestMass_prefixNormalized_eq q m hm hr
  have hden : 0 < 1 - residualMass q (Finset.range m) := by linarith
  have hmax : ∀ i, (prefixNormalizedLaw q m).mass i ≤
      (prefixNormalizedLaw q m).mass (largestIndex q) := by
    intro i
    rw [prefixNormalizedLaw_mass q m (largestIndex q) hr, if_pos hm, ← largestMass_eq_selected, ← hmass,
      largestMass_eq_selected (prefixNormalizedLaw q m)]
    exact largestIndex_spec _ i
  have hle : largestIndex (prefixNormalizedLaw q m) ≤ largestIndex q := Nat.sInf_le hmax
  have hlt := hle.trans_lt hm
  have hmax' : ∀ i, q.mass i ≤ q.mass (largestIndex (prefixNormalizedLaw q m)) := by
    intro i
    have hsel := largestMass_eq_selected (prefixNormalizedLaw q m)
    rw [hmass, prefixNormalizedLaw_mass q m _ hr, if_pos hlt] at hsel
    have he := (div_left_inj' (ne_of_gt hden)).mp hsel
    rw [← he, largestMass_eq_selected]
    exact largestIndex_spec q i
  exact Nat.le_antisymm hle (Nat.sInf_le hmax')

theorem largestMass_prefixNormalized_tendsto (q : DiscreteLaw) :
    Tendsto (fun m => largestMass (prefixNormalizedLaw q m)) atTop (𝓝 (largestMass q)) := by
  have he : (fun m => largestMass (prefixNormalizedLaw q m)) =ᶠ[atTop]
      (fun m => largestMass q / (1 - residualMass q (Finset.range m))) := by
    filter_upwards [eventually_gt_atTop (largestIndex q), eventually_prefix_residual_lt_one q]
      with m hm hr
    exact largestMass_prefixNormalized_eq q m hm hr
  apply Tendsto.congr' he.symm
  simpa using tendsto_const_nhds.div
    (tendsto_const_nhds.sub (prefixResidual_tendsto_zero q)) (by norm_num : (1 : ℝ) - 0 ≠ 0)

theorem eventually_prefixNormalized_cap_four_fifths (q : DiscreteLaw)
    (hq : largestMass q ≤ 3 / 4) :
    ∀ᶠ m in atTop, largestMass (prefixNormalizedLaw q m) ≤ 4 / 5 :=
  ((largestMass_prefixNormalized_tendsto q).eventually
    (gt_mem_nhds (by linarith : largestMass q < 4 / 5))).mono (fun _ h => h.le)

theorem normalized_tail_mass_formula (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) < 1) :
    1 - largestMass (prefixNormalizedLaw q m) =
      (1 - largestMass q - residualMass q (Finset.range m)) /
        (1 - residualMass q (Finset.range m)) := by
  rw [largestMass_prefixNormalized_eq q m hm hr]
  have hden : 1 - residualMass q (Finset.range m) ≠ 0 := by linarith
  field_simp [hden]
  <;> ring

theorem normalized_tail_mass_tendsto (q : DiscreteLaw) :
    Tendsto (fun m => 1 - largestMass (prefixNormalizedLaw q m)) atTop
      (𝓝 (1 - largestMass q)) :=
  tendsto_const_nhds.sub (largestMass_prefixNormalized_tendsto q)

theorem allocationD_tail_prefixNormalized_tendsto (q : DiscreteLaw) (t : ℝ) :
    Tendsto (fun m => allocationD (tailMasses (prefixNormalizedLaw q m)) t) atTop
      (𝓝 (allocationD (tailMasses q) t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
    (prefixNormalized_l1_tendsto_zero q)
  filter_upwards [eventually_gt_atTop (largestIndex q), eventually_prefix_residual_lt_one q]
    with m hm hr
  apply (allocationD_abs_sub_le_l1 t (tailMasses_nonneg _) (tailMasses_nonneg _)
    (tailMasses_summable _) (tailMasses_summable _)).trans
  apply ((tailMasses_summable _).sub (tailMasses_summable _)).abs.tsum_le_tsum _
    ((prefixNormalizedLaw q m).summable_abs_sub q)
  intro i
  simp only [tailMasses, largestIndex_prefixNormalized_eq q m hm hr]
  split_ifs
  · simpa using abs_nonneg ((prefixNormalizedLaw q m).mass i - q.mass i)
  · exact le_rfl

theorem heavyAllocationFunction_prefixNormalized_tendsto (q : DiscreteLaw) (t : ℝ) :
    Tendsto (fun m => heavyAllocationFunction (prefixNormalizedLaw q m) t) atTop
      (𝓝 (heavyAllocationFunction q t)) :=
  (allocationD_tail_prefixNormalized_tendsto q t).add
    (((normalized_tail_mass_tendsto q).div_const t).sqrt)

theorem heavyRoot_prefixNormalized_tendsto_targets (q : DiscreteLaw)
    (hq : largestMass q < 1) {em : ℕ → ℝ} {e : ℝ}
    (he : 0 < e) (hem : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => heavyRoot (prefixNormalizedLaw q m) (em m)) atTop
      (𝓝 (heavyRoot q e)) := by
  have hspec := heavyRoot_spec q hq he
  apply tendsto_positive_roots (f := heavyAllocationFunction q)
    (fm := fun m => heavyAllocationFunction (prefixNormalizedLaw q m))
    (em := em) hspec.1 hspec.2 (strictAntiOn_heavyAllocationFunction q hq)
  · exact fun m => heavyAllocationFunction_antitone _
  · exact fun t _ => heavyAllocationFunction_prefixNormalized_tendsto q t
  · exact hem
  · filter_upwards [hem.eventually (lt_mem_nhds he),
      (largestMass_prefixNormalized_tendsto q).eventually (gt_mem_nhds hq)] with m hem hqm
    exact heavyRoot_spec _ hqm hem

theorem heavyRoot_prefixNormalized_plus_two_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => heavyRoot (prefixNormalizedLaw q m)
      (ε + 2 * residualMass q (Finset.range m))) atTop (𝓝 (heavyRoot q ε)) :=
  heavyRoot_prefixNormalized_tendsto_targets q hq hε (normalized_radius_tendsto q ε)

theorem heavyRoot_prefixNormalized_boundary_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) :
    Tendsto (fun m => heavyRoot (prefixNormalizedLaw q m)
      (1 - largestMass (prefixNormalizedLaw q m))) atTop
      (𝓝 (heavyRoot q (1 - largestMass q))) :=
  heavyRoot_prefixNormalized_tendsto_targets q hq (sub_pos.mpr hq)
    (normalized_tail_mass_tendsto q)

end IdentityTesting
