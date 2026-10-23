import IdentityTesting.CountableScaleBounds
import IdentityTesting.PoolingReverseTests

/-! A uniform complete finite-support upper bound lifts to the full original
countable problem. The finite reference and its valid radius are constructed. -/

noncomputable section
open Filter
namespace IdentityTesting

theorem countable_upper_of_finite_support_upper {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (k : ℕ) (p : FiniteTesting.Probability (Fin k)) (e : ℝ),
      0 < e → e < 1 →
      ∃ n : ℕ, HasIdentityTest (extendFiniteLaw p) e n ∧
        (n : ℝ) ≤ C * (roundedScale (extendFiniteLaw p) e : ℝ))
    (q : DiscreteLaw) (hq : largestMass q < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (2 * C) * (roundedScale q ε : ℝ) := by
  obtain ⟨m, h0, h1, hround⟩ :=
    (eventually_prefixPooled_radius_and_roundedScale q hq hε0 hε1).exists
  obtain ⟨n, htest, hn⟩ := hfinite (m + 1) (prefixPooledFinite q m)
    (ε - residualMass q (Finset.range m)) h0 h1
  rw [extendFiniteLaw_prefixPooledFinite] at htest hn
  refine ⟨n, hasIdentityTest_countable_of_prefixPooled q m ε n htest, ?_⟩
  have hround' :
      (roundedScale (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) : ℝ) ≤
        2 * (roundedScale q ε : ℝ) := by exact_mod_cast hround
  calc
    (n : ℝ) ≤ C *
        (roundedScale (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) : ℝ) := hn
    _ ≤ C * (2 * (roundedScale q ε : ℝ)) := mul_le_mul_of_nonneg_left hround' hC
    _ = (2 * C) * (roundedScale q ε : ℝ) := by ring

/-- The heavy branch alone can be supplied independently by its actual finite
tester. Prefix selection preserves the heavy branch and its nonpoint condition. -/
theorem countable_heavy_upper_of_finite_heavy_upper {C : ℝ} (hC : 0 ≤ C)
    (hfinite : ∀ (k : ℕ) (p : FiniteTesting.Probability (Fin k)) (e : ℝ),
      3 / 4 < largestMass (extendFiniteLaw p) → largestMass (extendFiniteLaw p) < 1 →
      0 < e → e < 1 →
      ∃ n : ℕ, HasIdentityTest (extendFiniteLaw p) e n ∧
        (n : ℝ) ≤ C * (roundedScale (extendFiniteLaw p) e : ℝ))
    (q : DiscreteLaw) (hh : 3 / 4 < largestMass q) (hq : largestMass q < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (2 * C) * (roundedScale q ε : ℝ) := by
  obtain ⟨m, hm, h0, h1, hround⟩ :=
    ((eventually_prefixPooled_head q).and
      (eventually_prefixPooled_radius_and_roundedScale q hq hε0 hε1)).exists
  obtain ⟨n, htest, hn⟩ := hfinite (m + 1) (prefixPooledFinite q m)
    (ε - residualMass q (Finset.range m))
    (by rw [extendFiniteLaw_prefixPooledFinite, hm.2.2.1]; exact hh)
    (by rw [extendFiniteLaw_prefixPooledFinite, hm.2.2.1]; exact hq) h0 h1
  rw [extendFiniteLaw_prefixPooledFinite] at htest hn
  refine ⟨n, hasIdentityTest_countable_of_prefixPooled q m ε n htest, ?_⟩
  have hround' :
      (roundedScale (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) : ℝ) ≤
        2 * (roundedScale q ε : ℝ) := by exact_mod_cast hround
  calc
    (n : ℝ) ≤ C *
        (roundedScale (prefixPooledLaw q m) (ε - residualMass q (Finset.range m)) : ℝ) := hn
    _ ≤ C * (2 * (roundedScale q ε : ℝ)) := mul_le_mul_of_nonneg_left hround' hC
    _ = (2 * C) * (roundedScale q ε : ℝ) := by ring

end IdentityTesting
