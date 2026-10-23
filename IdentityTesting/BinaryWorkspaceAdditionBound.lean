import IdentityTesting.BinaryWorkspaceRationalAdder
import IdentityTesting.BinaryRationalArithmeticAdderBound

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation

theorem rationalAdder_initial_cells (x y : BinaryRationalArithmetic.Word) :
    rationalAdderCells (BinaryRationalArithmeticAdder.initial x y) + 2 = x.length + y.length := by
  simp [rationalAdderCells, BinaryRationalArithmeticAdder.initial, rationalMultiplierCells,
    signedMultiplierCells, BinarySignedMultiplier.initial, multiplierCells,
    BinaryMultiplierMachine.ready, BinaryAdderMachine.haltState, adderCells,
    normalizerCells, rationalNormalizationCells, BinaryRationalNormalizationMachine.initial,
    gcdCells, BinaryGcdMachine.ready, divisionCells, BinaryDivisionMachine.initial,
    BinarySubtractorMachine.haltState, BinaryDivisionMachine.word,
    BinaryRationalArithmetic.Word.length, signedAdderCells, BinarySignedAdder.initial,
    signedComparisonCells, BinarySignedComparison.initial, BinaryAdderMachine.loopState]
  omega

theorem binary_rational_addition_with_cleanup (p q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticAdder.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      let final := BinaryRationalArithmeticAdder.advance steps s
      final.phase = .halt ∧ (BinaryRationalArithmeticAdder.output final).value = p+q ∧
      (∀ i, (BinaryWorkspaceCleanup.advance fuel
        (BinaryWorkspaceCleanup.initial (rationalAdderScratch final))).tapes i = []) ∧
      BinaryRationalArithmeticAdder.bitSteps steps s +
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalAdderScratch final)) ≤
          6000000 * (rationalEncodingLength p + rationalEncodingLength q + 1)^3 := by
  obtain ⟨steps, hhalt, hval, _, _, _, hcost⟩ :=
    BinaryRationalArithmeticAdder.binary_rational_addition_machine p q
  let s := BinaryRationalArithmeticAdder.initial
    (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel, hclear, hcleanCost⟩ := rationalAdder_cleanup_cost steps s
  refine ⟨steps, fuel, hhalt, hval, hclear, ?_⟩
  have hinit := rationalAdder_initial_cells (BinaryRationalArithmetic.encode p)
    (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length, BinaryRationalArithmetic.encode_length] at hinit
  change rationalAdderCells s + 2 = _ at hinit
  change BinaryRationalArithmeticAdder.bitSteps steps s ≤ _ at hcost
  change BinaryRationalArithmeticAdder.bitSteps steps s +
    BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial
      (rationalAdderScratch (BinaryRationalArithmeticAdder.advance steps s))) ≤ _
  let S := rationalEncodingLength p + rationalEncodingLength q + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
  change _ ≤ 6000000*S^3
  change BinaryRationalArithmeticAdder.bitSteps steps s ≤ 1300000*S^3 at hcost
  have hinitS : rationalAdderCells s ≤ S := by dsimp [S]; omega
  nlinarith only [hcleanCost, hcost, hinitS, hcube, hS]

end IdentityTesting.BinaryWorkspaceAdapters
