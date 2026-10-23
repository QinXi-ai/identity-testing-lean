import IdentityTesting.MinimumSampleComplexity
import IdentityTesting.HeavyUpperCharacterization
import IdentityTesting.HeavyExteriorRootLowerBound
import IdentityTesting.HeavyRootLowerBound

/-! The original heavy-head formulas on the closed domain 0<R<=1/4.
These wrappers use the actual heavy root and minimum natural sample count,
without entering the global complexityScale branch at h>3/4. -/

noncomputable section
namespace IdentityTesting
open FiniteTesting HeavySignedFamily FiniteAllocationUpper

theorem finite_heavy_interior_minimum_closed {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hεR : ε ≤ tailTotal q) :
    (1 / (10 : ℝ) ^ 10) * heavyRoot (extendFiniteLaw q) ε ≤
        (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ∧
      (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤
        (10 : ℝ) ^ 42 * heavyRoot (extendFiniteLaw q) ε := by
  have hε1 : ε < 1 := by linarith
  have hm := minimumSampleComplexity_isLeast (extendFiniteLaw q) hε0 hε1.le
  refine ⟨le_of_lt (lt_of_not_ge (fun hn =>
    no_identityTest_of_finite_heavyRoot q hq hR0 hR hε0 hεR _ hn hm.1)), ?_⟩
  obtain ⟨n, ht, hn⟩ := HeavyUpper.finite_heavy_upper_bound q hq hR0 hR hε0 hεR
  have hN : (minimumSampleComplexity (extendFiniteLaw q) ε : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm.2 ht
  have hh := largestMass_extendFiniteLaw_heavy q hR
  have htotal := reference_head_tail q
  have hroot := heavyRoot_pos (extendFiniteLaw q) (by rw [hh]; linarith) hε0
  exact hN.trans (hn.trans (mul_le_mul_of_nonneg_right
    (by norm_num [coarseSampleConstant]) hroot.le))

/-- The exterior upper tester chooses the smaller of the boundary-root and
count-test budgets, including R=1/4 and the equality of those budgets. -/
theorem finite_heavy_exterior_upper_closed {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {Δ : ℝ} (hΔ : 0 < Δ) (hε1 : tailTotal q + Δ < 1) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) (tailTotal q + Δ) n ∧
      (n : ℝ) ≤ (10 : ℝ) ^ 42 * min
        (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ) := by
  have htotal := reference_head_tail q
  have hRf : 1 - q.mass 0 = tailTotal q := by linarith
  have hh := largestMass_extendFiniteLaw_heavy q hR
  have hroot := heavyRoot_pos (extendFiniteLaw q) (by rw [hh]; linarith) hR0
  by_cases hmin : heavyRoot (extendFiniteLaw q) (tailTotal q) ≤ tailTotal q / Δ ^ 2 + 1 / Δ
  · rw [min_eq_left hmin]
    obtain ⟨n, ht, hn⟩ := HeavyUpper.finite_heavy_upper_bound q hq hR0 hR hR0 le_rfl
    refine ⟨n, ht.mono_radius (by linarith), hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by norm_num [coarseSampleConstant]) hroot.le
  · rw [min_eq_right (le_of_not_ge hmin)]
    obtain ⟨n, ht, hn⟩ := HeavyExteriorTesting.finite_exterior_count_upper q 0 Δ hΔ (by rwa [hRf])
    rw [hRf] at ht hn
    refine ⟨n, ht, hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- `hh:exterior-law` with its literal minimum, on the original closed heavy
domain, for the original Nat observation alphabet with extra zero labels. -/
theorem finite_heavy_exterior_minimum_closed {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {Δ : ℝ} (hΔ : 0 < Δ) (hε1 : tailTotal q + Δ < 1) :
    (1 / (10 : ℝ) ^ 11) * min
        (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ) ≤
      (minimumSampleComplexity (extendFiniteLaw q) (tailTotal q + Δ) : ℝ) ∧
    (minimumSampleComplexity (extendFiniteLaw q) (tailTotal q + Δ) : ℝ) ≤
      (10 : ℝ) ^ 42 * min
        (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ) := by
  have hε0 : 0 < tailTotal q + Δ := add_pos hR0 hΔ
  have hm := minimumSampleComplexity_isLeast (extendFiniteLaw q) hε0 hε1.le
  refine ⟨le_of_lt (lt_of_not_ge (fun hn =>
    no_identityTest_of_finite_heavy_exterior q hq hR0 hR hΔ hε1 _ hn hm.1)), ?_⟩
  obtain ⟨n, ht, hn⟩ := finite_heavy_exterior_upper_closed q hq hR0 hR hΔ hε1
  exact (show (minimumSampleComplexity (extendFiniteLaw q) (tailTotal q + Δ) : ℝ) ≤ (n : ℝ) by
    exact_mod_cast hm.2 ht).trans hn

end IdentityTesting
