import IdentityTesting.CountableModel
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

/-- A positive root of a strictly decreasing function equals the infimum of its
positive sublevel set.  This explicitly checks the root encoding used in Target. -/
theorem positive_sublevel_sInf_eq {f : ℝ → ℝ} {e x : ℝ}
    (hf : StrictAntiOn f (Ioi 0)) (hx : 0 < x) (hfx : f x = e) :
    sInf {t : ℝ | 0 < t ∧ f t ≤ e} = x := by
  have hset : {t : ℝ | 0 < t ∧ f t ≤ e} = Ici x := by
    ext t
    constructor
    · rintro ⟨ht, hft⟩
      by_contra hxt
      have hlt : t < x := lt_of_not_ge hxt
      have hstrict := hf ht hx hlt
      rw [hfx] at hstrict
      exact (not_lt_of_ge hft) hstrict
    · intro hxt
      have ht : 0 < t := hx.trans_le hxt
      exact ⟨ht, hfx ▸ hf.antitoneOn hx ht hxt⟩
  rw [hset, csInf_Ici]

theorem exists_unique_positive_root {f : ℝ → ℝ} {S e : ℝ}
    (hc : ContinuousOn f (Ioi 0)) (hm : StrictAntiOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 S))
    (hinfty : Tendsto f atTop (𝓝 0)) (he : 0 < e) (heS : e < S) :
    ∃! t : ℝ, 0 < t ∧ f t = e := by
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), e < f t :=
    hzero.eventually (lt_mem_nhds heS)
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨l, hfl, hl⟩ := (hnear.and hpositive).exists
  have hfar : ∀ᶠ t in atTop, f t < e := hinfty.eventually (gt_mem_nhds he)
  obtain ⟨r, hfr, hlr⟩ := (hfar.and (eventually_ge_atTop l)).exists
  have hcont : ContinuousOn f (Icc l r) :=
    hc.mono (fun t ht => hl.trans_le ht.1)
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hlr hcont ⟨hfr.le, hfl.le⟩
  have ht0 : 0 < t := hl.trans_le ht.1
  refine ⟨t, ⟨ht0, hft⟩, ?_⟩
  intro y hy
  exact hm.injOn hy.1 ht0 (hy.2.trans hft.symm)

theorem positive_sublevel_sInf_is_root {f : ℝ → ℝ} {S e : ℝ}
    (hc : ContinuousOn f (Ioi 0)) (hm : StrictAntiOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 S))
    (hinfty : Tendsto f atTop (𝓝 0)) (he : 0 < e) (heS : e < S) :
    0 < sInf {t : ℝ | 0 < t ∧ f t ≤ e} ∧
      f (sInf {t : ℝ | 0 < t ∧ f t ≤ e}) = e := by
  obtain ⟨t, ht, _⟩ := exists_unique_positive_root hc hm hzero hinfty he heS
  rw [positive_sublevel_sInf_eq hm ht.1 ht.2]
  exact ht

theorem exists_unique_positive_root_of_top_limit {f : ℝ → ℝ} {e : ℝ}
    (hc : ContinuousOn f (Ioi 0)) (hm : StrictAntiOn f (Ioi 0))
    (hzero : Tendsto f (𝓝[>] (0 : ℝ)) atTop)
    (hinfty : Tendsto f atTop (𝓝 0)) (he : 0 < e) :
    ∃! t : ℝ, 0 < t ∧ f t = e := by
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), e < f t := by
    filter_upwards [(tendsto_atTop.1 hzero) (e + 1)] with t ht
    linarith
  have hpositive : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨l, hfl, hl⟩ := (hnear.and hpositive).exists
  have hfar : ∀ᶠ t in atTop, f t < e := hinfty.eventually (gt_mem_nhds he)
  obtain ⟨r, hfr, hlr⟩ := (hfar.and (eventually_ge_atTop l)).exists
  have hcont : ContinuousOn f (Icc l r) :=
    hc.mono (fun t ht => hl.trans_le ht.1)
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hlr hcont ⟨hfr.le, hfl.le⟩
  have ht0 : 0 < t := hl.trans_le ht.1
  refine ⟨t, ⟨ht0, hft⟩, ?_⟩
  intro y hy
  exact hm.injOn hy.1 ht0 (hy.2.trans hft.symm)

end IdentityTesting
