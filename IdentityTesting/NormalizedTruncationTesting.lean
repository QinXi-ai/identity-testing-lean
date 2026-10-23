import IdentityTesting.CountableProductTV
import IdentityTesting.HundredBatchHoeffding
import IdentityTesting.NormalizedTruncationBranches

/-! The original normalized-truncation transfer with 100 independent batches.
The test operates on the original Nat alphabet, including every zero-reference
label, and its internal Bernoulli coins are integrated in hundredBatchTest. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem normalized_hundred_batch_test (q : DiscreteLaw) (m n : ℕ) (ε : ℝ)
    (hr : residualMass q (Finset.range m) < 1)
    (hnr : (n : ℝ) * residualMass q (Finset.range m) ≤ 1 / 24)
    (test : RandomizedTest n) (htest : IsIdentityTest q ε test) :
    IsIdentityTest (prefixNormalizedLaw q m)
      (ε + 2 * residualMass q (Finset.range m)) (hundredBatchTest test) := by
  obtain ⟨hnull, halt⟩ := normalized_test_errors q m n ε hr hnr test htest
  constructor
  · exact (hundredBatchTest_null_error _ test hnull).trans hundred_batch_exp_lt_third.le
  · intro p hp
    have h : acceptanceProbability p test ≤ 3 / 8 := by linarith [halt p hp]
    exact (hundredBatchTest_alternative_error p test h).trans hundred_batch_exp_lt_third.le

theorem eventually_normalized_transfer_parameters (q : DiscreteLaw) (n : ℕ)
    {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ m in atTop, residualMass q (Finset.range m) < 1 ∧
      (n : ℝ) * residualMass q (Finset.range m) ≤ 1 / 24 ∧
      ε + 2 * residualMass q (Finset.range m) < 1 := by
  have hn : Tendsto (fun m => (n : ℝ) * residualMass q (Finset.range m)) atTop (𝓝 0) := by
    simpa using (prefixResidual_tendsto_zero q).const_mul (n : ℝ)
  filter_upwards [eventually_prefix_residual_lt_one q,
    hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 24)),
    (normalized_radius_tendsto q ε).eventually (gt_mem_nhds hε)] with m hm hn he
  exact ⟨hm, hn.le, he⟩

/-- Every original n-sample test gives actual 100n-sample tests for all sufficiently
large normalized finite references, at the manuscript's radius epsilon + 2r. -/
theorem eventually_normalized_hasIdentityTest (q : DiscreteLaw) (n : ℕ)
    {ε : ℝ} (hε : ε < 1) (htest : HasIdentityTest q ε n) :
    ∀ᶠ m in atTop, HasIdentityTest (prefixNormalizedLaw q m)
      (ε + 2 * residualMass q (Finset.range m)) (100 * n) := by
  obtain ⟨test, ht⟩ := htest
  filter_upwards [eventually_normalized_transfer_parameters q n hε] with m hm
  exact ⟨hundredBatchTest test, normalized_hundred_batch_test q m n ε hm.1 hm.2.1 test ht⟩

end IdentityTesting
