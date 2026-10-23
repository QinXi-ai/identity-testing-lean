import IdentityTesting.CountableLowerApproximation
import IdentityTesting.PoolingReverseTests
import IdentityTesting.FiniteTestingRelabeling

/-! The finite prior lower bound applies to every original countable reference
with capped largest atom. Finite support, positivity, and limit premises are
constructed internally. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting
open FiniteTesting

theorem no_identityTest_countable_allocation_root (q : DiscreteLaw)
    (hcap : largestMass q ≤ (4 : ℝ) / 5) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (2 * (10 : ℝ) ^ 12)) * allocationRoot q ε) :
    ¬ HasIdentityTest q ε n := by
  intro htest
  have hsmall : ∀ᶠ m in atTop, residualMass q (Finset.range m) < 1 - ε :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds (sub_pos.mpr hε1))
  obtain ⟨m, hm, hsmall, hroot⟩ :=
    (eventually_prefixPooled_head q |>.and
      (hsmall.and (eventually_allocationRoot_prefixPooled_plus_ge_half q hε0 hε1))).exists
  have hmcap : ∀ i, (prefixPooledFinite q m).mass i ≤ (4 : ℝ) / 5 := by
    intro i
    calc
      (prefixPooledFinite q m).mass i ≤ largestMass (prefixPooledLaw q m) := by
        rw [largestMass_eq_selected]
        exact largestIndex_spec (prefixPooledLaw q m) i.val
      _ = largestMass q := hm.2.2.1
      _ ≤ 4 / 5 := hcap
  have hres : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
  have hlow := no_identityTest_of_general_allocation_root_with_zeros
    (prefixPooledFinite q m) hmcap (ε + residualMass q (Finset.range m))
    (add_pos_of_pos_of_nonneg hε0 hres) (by linarith) n (by
      rw [extendFiniteLaw_prefixPooledFinite]
      nlinarith only [hn, hroot])
  apply hlow
  rw [extendFiniteLaw_prefixPooledFinite]
  exact hasIdentityTest_prefixPooled_of_countable q m ε n htest

theorem allocation_branch_lower (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hcap : largestMass q ≤ 3 / 4)
    (hbranch : largestMass q / 2 ≤ 1 - ε) (n : ℕ) (htest : HasIdentityTest q ε n) :
    (1 / (4 * (10 : ℝ) ^ 12)) * (roundedScale q ε : ℝ) ≤ n := by
  have hcap' : largestMass q ≤ (4 : ℝ) / 5 := hcap.trans (by norm_num)
  have hnroot : (1 / (2 * (10 : ℝ) ^ 12)) * allocationRoot q ε < n :=
    lt_of_not_ge (fun hn => no_identityTest_countable_allocation_root q hcap' ε hε0 hε1 n hn htest)
  have hnzero : n ≠ 0 := by
    intro hn
    subst n
    exact no_zero_sample_test q ε hε1 htest
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnzero
  have hscale : complexityScale q ε = allocationRoot q ε := by
    have hpoint : largestMass q ≠ 1 := ne_of_lt (hcap.trans_lt (by norm_num))
    simp only [complexityScale, ne_of_lt hε1, hpoint, not_lt.mpr hcap,
      hbranch, if_false, if_true]
  have hround : (roundedScale q ε : ℝ) < allocationRoot q ε + 1 := by
    unfold roundedScale
    rw [hscale]
    exact Nat.ceil_lt_add_one (allocationRoot_spec q hε0 hε1).1.le
  nlinarith only [hnroot, hn1, hround]

end IdentityTesting
