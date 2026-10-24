import IdentityTesting.BinaryWorkspaceRationalComparisonCost

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation
open scoped BigOperators

theorem rationalComparison_cleanup (s : BinaryRationalArithmeticComparison.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalComparisonScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalComparisonScratch s)) ≤
        3*(94+rationalComparisonCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalComparisonScratch s)
  dsimp only at h
  refine ⟨94+∑ i,(rationalComparisonScratch s i).length,h.2.1,?_⟩
  have hs := rationalComparisonScratch_cells s
  exact h.2.2.trans (Nat.mul_le_mul_left 3 (by omega))

theorem rationalComparison_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticComparison.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalComparisonScratch (BinaryRationalArithmeticComparison.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalComparisonScratch (BinaryRationalArithmeticComparison.advance n s))) ≤
        3*(94+rationalComparisonCells s+BinaryRationalArithmeticComparison.bitSteps n s) := by
  obtain ⟨fuel,hc,hb⟩ := rationalComparison_cleanup (BinaryRationalArithmeticComparison.advance n s)
  refine ⟨fuel,hc,?_⟩
  have hg := rationalComparison_cells_cost n s
  exact hb.trans (Nat.mul_le_mul_left 3 (by omega))

theorem binary_rational_comparison_with_cleanup (p q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticComparison.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      let final := BinaryRationalArithmeticComparison.advance steps s
      final.phase = .halt ∧ BinaryRationalArithmeticComparison.output final = BinaryRationalArithmetic.encode (if p≤q then 1 else 0) ∧
      (∀ i, (BinaryWorkspaceCleanup.advance fuel (BinaryWorkspaceCleanup.initial (rationalComparisonScratch final))).tapes i = []) ∧
      BinaryRationalArithmeticComparison.bitSteps steps s+
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalComparisonScratch final)) ≤
          23000000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  obtain ⟨steps,hh,hv,hb⟩ := BinaryRationalArithmeticComparison.binary_rational_comparison_machine p q
  let s := BinaryRationalArithmeticComparison.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel,hc,hb'⟩ := rationalComparison_cleanup_cost steps s
  refine ⟨steps,fuel,hh,hv,hc,?_⟩
  have hi := rationalAdder_initial_cells (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length,BinaryRationalArithmetic.encode_length] at hi
  have hi' : rationalComparisonCells s+2 = rationalEncodingLength p+rationalEncodingLength q := by
    simpa [rationalComparisonCells,s,BinaryRationalArithmeticComparison.initial,
      rationalSubtractorCells,BinaryRationalArithmeticSubtractor.initial] using hi
  change BinaryRationalArithmeticComparison.bitSteps steps s ≤ _ at hb
  change BinaryRationalArithmeticComparison.bitSteps steps s+_ ≤ _
  let S := rationalEncodingLength p+rationalEncodingLength q+1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS,Nat.mul_le_mul_left S hS]
  have hiS : rationalComparisonCells s ≤ S := by dsimp [S]; omega
  change _ ≤ 23000000*S^3
  change BinaryRationalArithmeticComparison.bitSteps steps s ≤ 5500000*S^3 at hb
  nlinarith only [hb,hb',hiS,hcube,hS]

end IdentityTesting.BinaryWorkspaceAdapters
