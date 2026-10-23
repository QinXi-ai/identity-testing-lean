import IdentityTesting.CountableLowerBound
import IdentityTesting.CountableAllocationUpperBound
import IdentityTesting.CountableMomentBranch

/-! Complete original-model characterization for largest reference atom at most 3/4. -/
noncomputable section
namespace IdentityTesting

theorem nonheavy_characterization (q : DiscreteLaw) (ε : ℝ)
    (hcap : largestMass q ≤ (3 : ℝ) / 4) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ n : ℕ, HasIdentityTest q ε n →
      (1 / (4 * (10 : ℝ) ^ 12)) * (roundedScale q ε : ℝ) ≤ n) ∧
    (∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (10 : ℝ) ^ 42 * (roundedScale q ε : ℝ)) := by
  refine ⟨countable_characterization_lower q ε hε0 hε1, ?_⟩
  by_cases hε : ε = 1
  · subst ε
    exact ⟨0, radius_one_zero_samples q, by simp⟩
  have he1 : ε < 1 := lt_of_le_of_ne hε1 hε
  have hr : 0 ≤ (roundedScale q ε : ℝ) := Nat.cast_nonneg _
  by_cases hb : largestMass q / 2 ≤ 1 - ε
  · obtain ⟨n, ht, hn⟩ := allocation_branch_upper q ε hε0 he1 hcap hb
    exact ⟨n, ht, hn.trans (mul_le_mul_of_nonneg_right
      (by norm_num [FiniteAllocationUpper.coarseSampleConstant]) hr)⟩
  · obtain ⟨n, ht, hn⟩ := moment_branch_upper q ε hε0 he1 hcap (lt_of_not_ge hb)
    exact ⟨n, ht, hn.trans (mul_le_mul_of_nonneg_right (by norm_num) hr)⟩

end IdentityTesting
