import IdentityTesting.CountableMomentTesting
import IdentityTesting.CountableScaleBounds

/-! The moment upper branch expressed in the original rounded-scale contract. -/

noncomputable section
namespace IdentityTesting

theorem moment_branch_upper (q : DiscreteLaw) (ε : ℝ)
    (_hε0 : 0 < ε) (hε1 : ε < 1) (hcap : largestMass q ≤ 3 / 4)
    (hbranch : 1 - ε < largestMass q / 2) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ 200000000000000 * (roundedScale q ε : ℝ) := by
  have hhead : 2 * (1 - ε) < largestMass q := by linarith
  obtain ⟨n, htest, hn⟩ := hasIdentityTest_moment_countable q (1 - ε) (sub_pos.mpr hε1) hhead
  have hscale : complexityScale q ε = 1 / overlapMoment q (1 - ε) := by
    have hpoint : largestMass q ≠ 1 := ne_of_lt (hcap.trans_lt (by norm_num))
    simp only [complexityScale, ne_of_lt hε1, hpoint, not_lt.mpr hcap,
      not_le.mpr hbranch, if_false]
  refine ⟨n, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using htest
  · have hceil : 1 / overlapMoment q (1 - ε) ≤ (roundedScale q ε : ℝ) := by
      rw [← hscale]
      exact Nat.le_ceil _
    calc
      (n : ℝ) ≤ 200000000000000 / overlapMoment q (1 - ε) := hn
      _ = 200000000000000 * (1 / overlapMoment q (1 - ε)) := by ring
      _ ≤ 200000000000000 * (roundedScale q ε : ℝ) :=
        mul_le_mul_of_nonneg_left hceil (by norm_num)

end IdentityTesting
