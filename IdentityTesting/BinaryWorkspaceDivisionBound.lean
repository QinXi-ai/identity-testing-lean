import IdentityTesting.BinaryWorkspaceRationalDivider
import IdentityTesting.BinaryRationalArithmeticDividerBound

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation

theorem rationalDivider_initial_cells (x y : BinaryRationalArithmetic.Word) :
    rationalDividerCells (BinaryRationalArithmeticDivider.initial x y) + 2 = x.length + y.length := by
  simp [rationalDividerCells, BinaryRationalArithmeticDivider.initial,
    BinaryRationalArithmeticDivider.reciprocalLayout, rationalMultiplierCells,
    BinaryRationalArithmeticMultiplier.initial, signedMultiplierCells, BinarySignedMultiplier.initial,
    multiplierCells, BinaryMultiplierMachine.ready, BinaryAdderMachine.haltState, adderCells,
    normalizerCells, rationalNormalizationCells, BinaryRationalNormalizationMachine.initial,
    gcdCells, BinaryGcdMachine.ready, divisionCells, BinaryDivisionMachine.initial,
    BinarySubtractorMachine.haltState, BinaryDivisionMachine.word, BinaryRationalArithmetic.Word.length]
  omega

theorem binary_rational_division_with_cleanup (p q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticDivider.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      let final := BinaryRationalArithmeticDivider.advance steps s
      (final.phase = .halt ∨ final.phase = .zeroHalt) ∧
      (BinaryRationalArithmeticDivider.output final).value = p/q ∧
      (∀ i, (BinaryWorkspaceCleanup.advance fuel
        (BinaryWorkspaceCleanup.initial (rationalDividerScratch final))).tapes i = []) ∧
      BinaryRationalArithmeticDivider.bitSteps steps s +
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalDividerScratch final)) ≤
          300000 * (rationalEncodingLength p + rationalEncodingLength q + 1)^3 := by
  obtain ⟨steps, hhalt, hval, _, _, _, hcost⟩ :=
    BinaryRationalArithmeticDivider.binary_rational_division_machine p q
  let s := BinaryRationalArithmeticDivider.initial
    (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel, hclear, hcleanCost⟩ := rationalDivider_cleanup_cost steps s
  refine ⟨steps, fuel, hhalt, hval, hclear, ?_⟩
  have hinit := rationalDivider_initial_cells (BinaryRationalArithmetic.encode p)
    (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length, BinaryRationalArithmetic.encode_length] at hinit
  change rationalDividerCells s + 2 = _ at hinit
  change BinaryRationalArithmeticDivider.bitSteps steps s ≤ _ at hcost
  change BinaryRationalArithmeticDivider.bitSteps steps s +
    BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial
      (rationalDividerScratch (BinaryRationalArithmeticDivider.advance steps s))) ≤ _
  let S := rationalEncodingLength p + rationalEncodingLength q + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
  change _ ≤ 300000*S^3
  change BinaryRationalArithmeticDivider.bitSteps steps s ≤ 50000*S^3 at hcost
  have hinitS : rationalDividerCells s ≤ S := by dsimp [S]; omega
  nlinarith only [hcleanCost, hcost, hinitS, hcube, hS]

end IdentityTesting.BinaryWorkspaceAdapters
