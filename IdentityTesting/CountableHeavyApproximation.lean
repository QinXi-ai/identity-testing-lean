import IdentityTesting.CountableHeadApproximation
import IdentityTesting.CountableRootApproximation

/-! Actual heavy-root convergence for normalized finite pooled references.
No approximation premise is supplied by the caller: the original allocation
supremum and the selected largest atom determine the approximants. -/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

theorem heavyRoot_prefixPooled_tendsto_targets (q : DiscreteLaw)
    (hq : largestMass q < 1) {em : ℕ → ℝ} {e : ℝ}
    (he : 0 < e) (hem : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => heavyRoot (prefixPooledLaw q m) (em m)) atTop
      (𝓝 (heavyRoot q e)) := by
  have hspec := heavyRoot_spec q hq he
  apply tendsto_positive_roots (f := heavyAllocationFunction q)
    (fm := fun m => heavyAllocationFunction (prefixPooledLaw q m))
    (em := em) hspec.1 hspec.2 (strictAntiOn_heavyAllocationFunction q hq)
  · exact fun m => heavyAllocationFunction_antitone _
  · intro t _
    exact heavyAllocationFunction_prefixPooled_tendsto q t
  · exact hem
  · have hpositive : ∀ᶠ m in atTop, 0 < em m := hem.eventually (lt_mem_nhds he)
    filter_upwards [eventually_prefixPooled_head q, hpositive] with m hm hem
    exact heavyRoot_spec (prefixPooledLaw q m) (by simpa only [hm.2.2.1] using hq) hem

theorem heavyRoot_prefixPooled_shifted_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => heavyRoot (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m))) atTop (𝓝 (heavyRoot q ε)) := by
  apply heavyRoot_prefixPooled_tendsto_targets q hq hε
  have hc : Tendsto (fun _ : ℕ => ε) atTop (𝓝 ε) := tendsto_const_nhds
  simpa only [sub_zero] using hc.sub (prefixResidual_tendsto_zero q)

theorem heavyRoot_prefixPooled_tendsto (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => heavyRoot (prefixPooledLaw q m) ε) atTop (𝓝 (heavyRoot q ε)) :=
  heavyRoot_prefixPooled_tendsto_targets q hq hε tendsto_const_nhds

theorem eventually_heavyRoot_prefixPooled_le_twice (q : DiscreteLaw)
    (hq : largestMass q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, heavyRoot (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m)) ≤ 2 * heavyRoot q ε := by
  have hp := (heavyRoot_spec q hq hε).1
  have hlt : heavyRoot q ε < 2 * heavyRoot q ε := by linarith
  exact ((heavyRoot_prefixPooled_shifted_tendsto q hq hε).eventually
    (gt_mem_nhds hlt)).mono (fun _ h => h.le)

end IdentityTesting
