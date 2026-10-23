import IdentityTesting.CountableFiniteApproximation
import IdentityTesting.CountableRoots

/-! Root bracketing and actual allocation-root convergence for the finite
coarsenings, at the manuscript's shifted strict testing radius. -/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

/-- Positive roots of antitone approximants converge by bracketing the limiting
strict root. Actual coarsened allocation functions discharge this interface below. -/
theorem tendsto_positive_roots {fm : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    {em xm : ℕ → ℝ} {e x : ℝ}
    (hx : 0 < x) (hfx : f x = e) (hf : StrictAntiOn f (Ioi 0))
    (hm : ∀ m, AntitoneOn (fm m) (Ioi 0))
    (hconv : ∀ t, 0 < t → Tendsto (fun m => fm m t) atTop (𝓝 (f t)))
    (he : Tendsto em atTop (𝓝 e))
    (hroots : ∀ᶠ m in atTop, 0 < xm m ∧ fm m (xm m) = em m) :
    Tendsto xm atTop (𝓝 x) := by
  apply tendsto_order.2
  constructor
  · intro a hax
    by_cases ha : 0 < a
    · have hgap : 0 < f a - e := by
        have h := hf ha hx hax
        rw [hfx] at h
        exact sub_pos.mpr h
      have hnear : ∀ᶠ m in atTop, 0 < fm m a - em m :=
        ((hconv a ha).sub he).eventually (lt_mem_nhds hgap)
      filter_upwards [hroots, hnear] with m hroot hnear
      by_contra hnot
      have hmono := hm m hroot.1 ha (le_of_not_gt hnot)
      rw [hroot.2] at hmono
      linarith
    · filter_upwards [hroots] with m hroot
      exact lt_of_le_of_lt (le_of_not_gt ha) hroot.1
  · intro b hxb
    have hb : 0 < b := hx.trans hxb
    have hgap : 0 < e - f b := by
      have h := hf hx hb hxb
      rw [hfx] at h
      exact sub_pos.mpr h
    have hnear : ∀ᶠ m in atTop, 0 < em m - fm m b :=
      (he.sub (hconv b hb)).eventually (lt_mem_nhds hgap)
    filter_upwards [hroots, hnear] with m hroot hnear
    by_contra hnot
    have hmono := hm m hb hroot.1 (le_of_not_gt hnot)
    rw [hroot.2] at hmono
    linarith

/-- The actual finite references at radius ε minus the residual mass have roots
converging to the original infimum-defined allocationRoot. -/
theorem allocationRoot_prefixPooled_tendsto (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun m => allocationRoot (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m))) atTop (𝓝 (allocationRoot q ε)) := by
  have hspec := allocationRoot_spec q hε0 hε1
  apply tendsto_positive_roots (f := allocationD q.mass)
    (fm := fun m => allocationD (prefixPooledLaw q m).mass)
    (em := fun m => ε - residualMass q (Finset.range m))
    hspec.1 hspec.2
    (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive)
  · intro m t ht r hr htr
    exact allocationD_antitone (prefixPooledLaw q m).nonneg
      (prefixPooledLaw q m).summable ht.le htr
  · intro t _
    exact allocationD_prefixPooled_tendsto q t
  · have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
    simpa only [sub_zero] using hc.sub (prefixResidual_tendsto_zero q)
  · have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < ε :=
      (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds hε0)
    filter_upwards [hsmall] with m hm
    have hr : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
    exact allocationRoot_spec (prefixPooledLaw q m) (sub_pos.mpr hm)
      ((sub_le_self ε hr).trans_lt hε1)

theorem eventually_allocationRoot_prefixPooled_le_twice (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ m in atTop, allocationRoot (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m)) ≤ 2 * allocationRoot q ε := by
  have hp := (allocationRoot_spec q hε0 hε1).1
  have hlt : allocationRoot q ε < 2 * allocationRoot q ε := by linarith
  exact ((allocationRoot_prefixPooled_tendsto q hε0 hε1).eventually
    (gt_mem_nhds hlt)).mono (fun _ h => h.le)

end IdentityTesting
