import IdentityTesting.CountableCharacterization
import IdentityTesting.ComplexityScaleRounding

noncomputable section
namespace IdentityTesting

/-- The statistical characterization directly in terms of the manuscript's real
scale. The existing lower and upper tests are reused; only rounding is removed. -/
theorem countable_characterization_realScale :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (q : DiscreteLaw) (ε : ℝ), 0 < ε → ε ≤ 1 →
        (∀ n : ℕ, HasIdentityTest q ε n → c * complexityScale q ε ≤ n) ∧
        (∃ n : ℕ, HasIdentityTest q ε n ∧ (n : ℝ) ≤ C * complexityScale q ε) := by
  obtain ⟨c, C, hc, hcC, h⟩ := countable_characterization
  have hC : 0 < C := hc.trans hcC
  refine ⟨c, 2 * C, hc, by linarith, ?_⟩
  intro q ε hε0 hε1
  obtain ⟨hl, hu⟩ := h q ε hε0 hε1
  constructor
  · intro n hn
    exact (mul_le_mul_of_nonneg_left (Nat.le_ceil (complexityScale q ε)) hc.le).trans (hl n hn)
  · obtain ⟨n, hn, hb⟩ := hu
    have hr : (roundedScale q ε : ℝ) ≤ 2 * complexityScale q ε := by
      rcases lt_or_eq_of_le hε1 with hlt | rfl
      · exact roundedScale_le_twice_complexityScale q hε0 hlt
      · simp [roundedScale, complexityScale]
    refine ⟨n, hn, ?_⟩
    calc
      (n : ℝ) ≤ C * roundedScale q ε := hb
      _ ≤ C * (2 * complexityScale q ε) := mul_le_mul_of_nonneg_left hr hC.le
      _ = (2 * C) * complexityScale q ε := by ring

end IdentityTesting
