import IdentityTesting.UnpoolingKernel
import IdentityTesting.PoolingTests
import IdentityTesting.CountableFiniteApproximation

/-! Exact reverse statistical transfer. Reference-conditional randomization
turns every original countable test into a test of the finite pooled reference
at the same strict radius and with the same sample size. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting
open FiniteTesting

theorem pooledLaw_totalVariation_le (p q : DiscreteLaw) (s : Finset ℕ) :
    FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) ≤ totalVariation p q := by
  have hp : residualOverlap p q s ≤ residualMass p s :=
    ((p.summable_min q).subtype {i | i ∉ s}).tsum_le_tsum
      (fun i => min_le_left _ _) (p.summable.subtype {i | i ∉ s})
  have hq : residualOverlap p q s ≤ residualMass q s :=
    ((p.summable_min q).subtype {i | i ∉ s}).tsum_le_tsum
      (fun i => min_le_right _ _) (q.summable.subtype {i | i ∉ s})
  have hmin := le_min hp hq
  rw [pooledLaw_totalVariation, totalVariation_eq_one_sub_overlap, ← overlap_split p q s]
  unfold pooledTVFormula
  linarith

theorem finite_pooled_test_of_countable_test (q : DiscreteLaw) (m : ℕ) (ε : ℝ) (n : ℕ)
    (htest : HasIdentityTest q ε n) :
    ∃ test : FiniteTesting.RandomizedTest (Fin n → PoolLabel (Finset.range m)),
      expectation (productLaw (pooledLaw q (Finset.range m)) n) test ≤ 1 / 3 ∧
      ∀ p : Probability (PoolLabel (Finset.range m)),
        ε < FiniteTesting.totalVariation p (pooledLaw q (Finset.range m)) →
          1 - expectation (productLaw p n) test ≤ 1 / 3 := by
  obtain ⟨test, hnull, halt⟩ := htest
  refine ⟨kernelAverageTest (unpoolingKernel q m) test, ?_, ?_⟩
  · rw [← rejectionProbability_countableMixture, countableMixture_unpooling_reference]
    exact hnull
  · intro p hp
    have htv := pooledLaw_totalVariation_le (countableMixture p (unpoolingKernel q m)) q
      (Finset.range m)
    rw [pooledLaw_countableMixture_unpooling] at htv
    have h := halt (countableMixture p (unpoolingKernel q m)) (hp.trans_le htv)
    rwa [acceptanceProbability_countableMixture] at h

theorem pooledLaw_prefixPooledLaw (q : DiscreteLaw) (m : ℕ) :
    pooledLaw (prefixPooledLaw q m) (Finset.range m) = pooledLaw q (Finset.range m) := by
  apply probability_ext
  intro y
  cases y with
  | none => exact prefixPooledLaw_discardedMass q m
  | some i => exact prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp i.property)

/-- This is a full original-model test at the finite coarsening, including
alternatives outside its finite reference support. The necessary radius loss
is explicit; a finite test alone would not cover those alternatives. -/
theorem hasIdentityTest_prefixPooled_of_countable (q : DiscreteLaw) (m : ℕ)
    (ε : ℝ) (n : ℕ) (htest : HasIdentityTest q ε n) :
    HasIdentityTest (prefixPooledLaw q m)
      (ε + residualMass q (Finset.range m)) n := by
  obtain ⟨test, hnull, halt⟩ := finite_pooled_test_of_countable_test q m ε n htest
  apply hasIdentityTest_of_pooled_test (prefixPooledLaw q m) (Finset.range m)
    (ε + residualMass q (Finset.range m)) n test
  · rwa [pooledLaw_prefixPooledLaw]
  · intro p hp
    apply halt p
    have hr : residualMass (prefixPooledLaw q m) (Finset.range m) =
        residualMass q (Finset.range m) := prefixPooledLaw_discardedMass q m
    simpa only [pooledLaw_prefixPooledLaw, hr, add_sub_cancel_right] using hp

/-- A complete test for the actual finite coarsening at the decreased radius
gives a complete test for the original countable reference. -/
theorem hasIdentityTest_countable_of_prefixPooled (q : DiscreteLaw) (m : ℕ)
    (ε : ℝ) (n : ℕ)
    (htest : HasIdentityTest (prefixPooledLaw q m)
      (ε - residualMass q (Finset.range m)) n) : HasIdentityTest q ε n := by
  obtain ⟨test, hnull, halt⟩ := finite_pooled_test_of_countable_test
    (prefixPooledLaw q m) m (ε - residualMass q (Finset.range m)) n htest
  apply hasIdentityTest_of_pooled_test q (Finset.range m) ε n test
  · simpa only [pooledLaw_prefixPooledLaw] using hnull
  · intro p hp
    apply halt p
    simpa only [pooledLaw_prefixPooledLaw] using hp

end IdentityTesting
