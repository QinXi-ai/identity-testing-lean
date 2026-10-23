import IdentityTesting.CountableHeavyLowerApproximation
import IdentityTesting.PoolingReverseTests
import IdentityTesting.HeavyRelabelingLowerBound

/-! Full heavy-branch lower bound for every original countable reference.
Both ε = tail mass and alternatives outside finite support are included. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem no_identityTest_countable_heavy_complexityScale (q : DiscreteLaw)
    (hh : (3 : ℝ) / 4 < largestMass q) (hh1 : largestMass q < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (2 * (10 : ℝ) ^ 11)) * complexityScale q ε) :
    ¬ HasIdentityTest q ε n := by
  intro htest
  have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < 1 - ε :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds (sub_pos.mpr hε1))
  obtain ⟨m, hm, hsmall, hscale⟩ :=
    (eventually_prefixPooled_head q |>.and (hsmall.and
      (eventually_heavy_complexityScale_prefixPooled_plus_ge_half q hh hh1 ε hε0 hε1))).exists
  have hres : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
  have hno := no_identityTest_of_finite_heavy_complexityScale_with_zeros
    (prefixPooledFinite q m)
    (by rw [extendFiniteLaw_prefixPooledFinite, hm.2.2.1]; exact hh)
    (by rw [extendFiniteLaw_prefixPooledFinite, hm.2.2.1]; exact hh1)
    (add_pos_of_pos_of_nonneg hε0 hres) (by linarith) n (by
      rw [extendFiniteLaw_prefixPooledFinite]
      nlinarith only [hn, hscale])
  apply hno
  rw [extendFiniteLaw_prefixPooledFinite]
  exact hasIdentityTest_prefixPooled_of_countable q m ε n htest

theorem heavy_branch_lower (q : DiscreteLaw)
    (hh : (3 : ℝ) / 4 < largestMass q) (hh1 : largestMass q < 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / (2 * (10 : ℝ) ^ 11)) * (roundedScale q ε : ℝ) ≤ n := by
  have hscale : (1 / (2 * (10 : ℝ) ^ 11)) * complexityScale q ε < (n : ℝ) :=
    lt_of_not_ge (fun hn => no_identityTest_countable_heavy_complexityScale q hh hh1 hε0 hε1 n hn htest)
  have hceil : roundedScale q ε ≤ 200000000000 * n := by
    apply Nat.ceil_le.mpr
    push_cast
    norm_num at hscale ⊢
    linarith only [hscale]
  have hreal : (roundedScale q ε : ℝ) ≤ 200000000000 * (n : ℝ) := by exact_mod_cast hceil
  norm_num
  linarith only [hreal]

end IdentityTesting
