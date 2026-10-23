import IdentityTesting.HeavyRestrictedSupportInterior
import IdentityTesting.HeavyRestrictedSupportNearExterior
import IdentityTesting.HeavyFiniteBridge

/-! The stronger heavy lower bounds with alternatives restricted to the
original positive support: direct finite tests and original Nat tests. -/

noncomputable section
namespace IdentityTesting.HeavyRestrictedSupport
open scoped BigOperators
open FiniteTesting HeavySignedFamily HeavyLowerGeometry

/-- Same Nat observations and same error thresholds as HasIdentityTest; only
the alternative family is restricted to the reference's positive support. -/
def HasPositiveSupportTest (q : DiscreteLaw) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ test : IdentityTesting.RandomizedTest n,
    rejectionProbability q test ≤ (1 : ℝ) / 3 ∧
      ∀ p : DiscreteLaw, (∀ i, q.mass i = 0 → p.mass i = 0) →
        ε < IdentityTesting.totalVariation p q → acceptanceProbability p test ≤ (1 : ℝ) / 3

theorem finite_supportTest_of_positiveSupportTest {k : ℕ}
    (q : Probability (Fin k)) (hq : ∀ i, 0 < q.mass i) (ε : ℝ) (n : ℕ)
    (ht : HasPositiveSupportTest (extendFiniteLaw q) ε n) : HasFiniteSupportTest q ε n := by
  obtain ⟨test, hnull, halt⟩ := ht
  refine ⟨restrictFiniteTest test, ?_, ?_⟩
  · rwa [← rejectionProbability_extendFiniteLaw]
  · intro p hp
    have hs : ∀ i, (extendFiniteLaw q).mass i = 0 → (extendFiniteLaw p).mass i = 0 := by
      intro i hi
      by_cases hik : i < k
      · have heq := extendFiniteLaw_mass_val q ⟨i, hik⟩
        have hpos : 0 < (extendFiniteLaw q).mass i := by rw [heq]; exact hq _
        exact False.elim ((ne_of_gt hpos) hi)
      · exact extendFiniteLaw_mass_of_not_lt p i hik
    have hsep : ε < IdentityTesting.totalVariation (extendFiniteLaw p) (extendFiniteLaw q) := by
      rwa [totalVariation_extendFiniteLaw]
    have he := halt (extendFiniteLaw p) hs hsep
    rwa [acceptanceProbability_extendFiniteLaw] at he

theorem no_supportTest_of_heavyRoot {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hεR : ε ≤ tailTotal q) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * heavyRoot (extendFiniteLaw q) ε) :
    ¬ HasFiniteSupportTest q ε n := by
  obtain ⟨hT, x, hx, hradius, hbudget⟩ :=
    exists_finite_heavy_coordinates_at_root q hq hR0 hR hε0
  exact no_supportTest_of_heavy_allocation_coordinates q x (heavyRoot (extendFiniteLaw q) ε) ε
    hT hq (fun i => ⟨(hx i).1.le, (hx i).2⟩) hR0 hR hbudget hradius hεR n hn

theorem no_supportTest_of_near_exterior {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ tailTotal q / 2) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 11) *
      min (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ)) :
    ¬ HasFiniteSupportTest q (tailTotal q + Δ) n := by
  have hc0 : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 11 := by norm_num
  have hnT := hn.trans (mul_le_mul_of_nonneg_left
    (min_le_left (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ)) hc0)
  have hncount := hn.trans (mul_le_mul_of_nonneg_left
    (min_le_right (heavyRoot (extendFiniteLaw q) (tailTotal q)) (tailTotal q / Δ ^ 2 + 1 / Δ)) hc0)
  obtain ⟨hT, x, hx, hboundary, hbudget⟩ :=
    exists_finite_heavy_coordinates_at_root q hq hR0 hR hR0
  have hnT' : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * heavyRoot (extendFiniteLaw q) (tailTotal q) :=
    hnT.trans (mul_le_mul_of_nonneg_right (by norm_num) hT.le)
  have hnΔ : (n : ℝ) * Δ ^ 2 / tailTotal q ≤ 1 / (10 : ℝ) ^ 10 := by
    have h := mul_le_mul_of_nonneg_right hncount (div_nonneg (sq_nonneg Δ) hR0.le)
    have heq : (1 / (10 : ℝ) ^ 11) * (tailTotal q / Δ ^ 2 + 1 / Δ) *
        (Δ ^ 2 / tailTotal q) = (1 / (10 : ℝ) ^ 11) * (1 + Δ / tailTotal q) := by
      field_simp [ne_of_gt hR0, ne_of_gt hΔ0]
      <;> ring
    rw [heq] at h
    have hratio : Δ / tailTotal q ≤ (1 : ℝ) / 2 :=
      (div_le_iff₀ hR0).2 (by linarith only [hΔ])
    have hmul : (n : ℝ) * (Δ ^ 2 / tailTotal q) = (n : ℝ) * Δ ^ 2 / tailTotal q := by ring
    rw [hmul] at h
    norm_num at h
    linarith only [h, hratio]
  exact no_supportTest_of_heavy_boundary_coordinates q x
    (heavyRoot (extendFiniteLaw q) (tailTotal q)) Δ hT hq
    (fun i => ⟨(hx i).1.le, (hx i).2⟩) hR0 hR hbudget hboundary hΔ0 hΔ n hnT' hnΔ

/-- The stronger final sentence of `hh:interior`: the lower bound already
holds against alternatives supported inside the original positive support. -/
theorem positive_support_heavy_interior_lower {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hεR : ε ≤ tailTotal q) (n : ℕ)
    (ht : HasPositiveSupportTest (extendFiniteLaw q) ε n) :
    (1 / (10 : ℝ) ^ 10) * heavyRoot (extendFiniteLaw q) ε < (n : ℝ) := by
  exact lt_of_not_ge (fun hn => no_supportTest_of_heavyRoot q hq hR0 hR hε0 hεR n hn
    (finite_supportTest_of_positiveSupportTest q hq ε n ht))

/-- The stronger final sentence of `hh:exterior` in its stated near-exterior
domain 0<Delta<=R/2, including R=1/4. -/
theorem positive_support_heavy_near_exterior_lower {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ : Δ ≤ tailTotal q / 2) (n : ℕ)
    (ht : HasPositiveSupportTest (extendFiniteLaw q) (tailTotal q + Δ) n) :
    (1 / (10 : ℝ) ^ 11) * min (heavyRoot (extendFiniteLaw q) (tailTotal q))
      (tailTotal q / Δ ^ 2 + 1 / Δ) < (n : ℝ) := by
  exact lt_of_not_ge (fun hn => no_supportTest_of_near_exterior q hq hR0 hR hΔ0 hΔ n hn
    (finite_supportTest_of_positiveSupportTest q hq (tailTotal q + Δ) n ht))

end IdentityTesting.HeavyRestrictedSupport
