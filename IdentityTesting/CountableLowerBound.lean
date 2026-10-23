import IdentityTesting.CountableAllocationLowerBound
import IdentityTesting.CountableMomentLowerBound
import IdentityTesting.CountableHeavyLowerBound
import IdentityTesting.DegenerateBranches

/-! The lower half of the original characterization, for every countable law
and every original radius. There is no finite-support or supplied-prior premise. -/
noncomputable section
namespace IdentityTesting

theorem countable_characterization_lower (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / (4 * (10 : ℝ) ^ 12)) * (roundedScale q ε : ℝ) ≤ n := by
  by_cases hε : ε = 1
  · subst ε
    simp
  have he1 : ε < 1 := lt_of_le_of_ne hε1 hε
  have hr : 0 ≤ (roundedScale q ε : ℝ) := Nat.cast_nonneg _
  by_cases hpoint : largestMass q = 1
  · exact (mul_le_mul_of_nonneg_right (by norm_num :
      (1 / (4 * (10 : ℝ) ^ 12)) ≤ 1 / 4) hr).trans
        (point_branch_lower q hpoint hε0 he1 n htest)
  have hh1 : largestMass q < 1 := lt_of_le_of_ne (largestMass_le_one q) hpoint
  by_cases hh : (3 : ℝ) / 4 < largestMass q
  · exact (mul_le_mul_of_nonneg_right (by norm_num :
      (1 / (4 * (10 : ℝ) ^ 12)) ≤ 1 / (2 * (10 : ℝ) ^ 11)) hr).trans
        (heavy_branch_lower q hh hh1 hε0 he1 n htest)
  have hcap : largestMass q ≤ (3 : ℝ) / 4 := le_of_not_gt hh
  by_cases hb : largestMass q / 2 ≤ 1 - ε
  · exact allocation_branch_lower q ε hε0 he1 hcap hb n htest
  · exact (mul_le_mul_of_nonneg_right (by norm_num :
      (1 / (4 * (10 : ℝ) ^ 12)) ≤ 1 / 4000) hr).trans
        (moment_branch_lower q ε hε0 he1 hcap (lt_of_not_ge hb) n htest)

end IdentityTesting
