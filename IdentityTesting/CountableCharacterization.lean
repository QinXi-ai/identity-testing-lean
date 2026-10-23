import IdentityTesting.HeavyUpperCharacterization
import IdentityTesting.NonheavyCharacterization

/-! The original countable characterization, assembled from actual tests and
the uniform original-model lower bound. No branch hypothesis remains. -/
noncomputable section
namespace IdentityTesting

theorem countable_characterization_upper (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (10 : ℝ) ^ 42 * (roundedScale q ε : ℝ) := by
  by_cases he : ε = 1
  · subst ε
    exact ⟨0, radius_one_zero_samples q, by simp⟩
  have he1 : ε < 1 := lt_of_le_of_ne hε1 he
  have hr : 0 ≤ (roundedScale q ε : ℝ) := Nat.cast_nonneg _
  by_cases hp : largestMass q = 1
  · exact ⟨roundedScale q ε, point_branch_upper q hp hε0 he1,
      by nlinarith only [hr]⟩
  have hq : largestMass q < 1 := lt_of_le_of_ne (largestMass_le_one q) hp
  by_cases hh : (3 : ℝ) / 4 < largestMass q
  · obtain ⟨n, ht, hn⟩ := countable_heavy_branch_upper q hh hq ε hε0 he1
    exact ⟨n, ht, hn.trans (mul_le_mul_of_nonneg_right (by norm_num) hr)⟩
  · exact (nonheavy_characterization q ε (le_of_not_gt hh) hε0 hε1).2

/-- The manuscript's original countable-support statistical characterization. -/
theorem countable_characterization : CountableCharacterization := by
  refine ⟨1 / (4 * (10 : ℝ) ^ 12), (10 : ℝ) ^ 42,
    by norm_num, by norm_num, ?_⟩
  intro q ε hε0 hε1
  exact ⟨countable_characterization_lower q ε hε0 hε1,
    countable_characterization_upper q ε hε0 hε1⟩

end IdentityTesting
