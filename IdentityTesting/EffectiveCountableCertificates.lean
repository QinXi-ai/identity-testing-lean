import IdentityTesting.EffectiveHeavyRoot
import IdentityTesting.EffectiveOverlapMoment

/-! Convergence of the concrete rational certificates returned by the effective
countable algorithms. Endpoint convergence is a consequence of certified width. -/
open scoped BigOperators
open Filter Topology
namespace IdentityTesting.RationalComputation

theorem rational_bracket_endpoints_tendsto {x : ℝ} (I : ℕ → ℚ × ℚ)
    (h : ∀ n, ((I n).1 : ℝ) ≤ x ∧ x ≤ ((I n).2 : ℝ) ∧
      (I n).2 - (I n).1 ≤ accessError n) :
    Tendsto (fun n => ((I n).1 : ℝ)) atTop (𝓝 x) ∧
      Tendsto (fun n => ((I n).2 : ℝ)) atTop (𝓝 x) := by
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ accessError_tendsto
    intro n
    have hn := h n
    have hw : ((I n).2 : ℝ) - ((I n).1 : ℝ) ≤ (accessError n : ℝ) := by
      exact_mod_cast hn.2.2
    rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hn.1)]
    linarith [hn.2.1]
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ accessError_tendsto
    intro n
    have hn := h n
    have hw : ((I n).2 : ℝ) - ((I n).1 : ℝ) ≤ (accessError n : ℝ) := by
      exact_mod_cast hn.2.2
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hn.2.1)]
    linarith [hn.1]

theorem countableAllocationRootInterval_tendsto {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (he : 0 < e) (her : e < ∑' i, a i) :
    let I := fun n => countableAllocationRootInterval A E ha hs he her
      (accessError n) (accessError_pos n)
    Tendsto (fun n => ((I n).1 : ℝ)) atTop (𝓝 (generalAllocationRoot a e)) ∧
      Tendsto (fun n => ((I n).2 : ℝ)) atTop (𝓝 (generalAllocationRoot a e)) := by
  apply rational_bracket_endpoints_tendsto
  intro n
  have h := countableAllocationRootInterval_spec A E ha hs he her
    (accessError n) (accessError_pos n)
  exact ⟨h.2.1.le, h.2.2.1.le, h.2.2.2⟩

theorem countableHeavyRootInterval_tendsto {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (hr : 0 < ∑' i, a i) (he : 0 < e) :
    let I := fun n => countableHeavyRootInterval A E ha hs hr he
      (accessError n) (accessError_pos n)
    Tendsto (fun n => ((I n).1 : ℝ)) atTop (𝓝 (generalHeavyRoot a (∑' i, a i) e)) ∧
      Tendsto (fun n => ((I n).2 : ℝ)) atTop (𝓝 (generalHeavyRoot a (∑' i, a i) e)) := by
  apply rational_bracket_endpoints_tendsto
  intro n
  have h := countableHeavyRootInterval_spec A E ha hs hr he
    (accessError n) (accessError_pos n)
  exact ⟨h.2.1.le, h.2.2.1.le, h.2.2.2⟩

theorem countableMomentInterval_tendsto {a : ℕ → ℝ} {δ : ℝ}
    (A : EffectiveMassAccess a) (D : EffectiveRealAccess δ) (hδ : 0 < δ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    let W := ∑' i, min (a i) ((a i) ^ (3 / 2 : ℝ) / Real.sqrt δ)
    let I := fun n => countableMomentInterval A D hδ (accessError n) (accessError_pos n)
    Tendsto (fun n => ((I n).1 : ℝ)) atTop (𝓝 W) ∧
      Tendsto (fun n => ((I n).2 : ℝ)) atTop (𝓝 W) := by
  apply rational_bracket_endpoints_tendsto
  intro n
  exact countableMomentInterval_spec A D hδ ha hs (accessError n) (accessError_pos n)

end IdentityTesting.RationalComputation
