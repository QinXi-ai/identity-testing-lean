import IdentityTesting.BinaryWorkspaceCost
import IdentityTesting.BinaryRationalArithmeticMultiplierBound

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation

theorem rationalMultiplier_initial_cells (x y : BinaryRationalArithmetic.Word) :
    rationalMultiplierCells (BinaryRationalArithmeticMultiplier.initial x y) + 2 = x.length + y.length := by
  simp [rationalMultiplierCells, BinaryRationalArithmeticMultiplier.initial,
    signedMultiplierCells, BinarySignedMultiplier.initial, multiplierCells,
    BinaryMultiplierMachine.ready, BinaryAdderMachine.haltState, adderCells,
    normalizerCells, rationalNormalizationCells, BinaryRationalNormalizationMachine.initial,
    gcdCells, BinaryGcdMachine.ready, divisionCells, BinaryDivisionMachine.initial,
    BinarySubtractorMachine.haltState, BinaryDivisionMachine.word,
    BinaryRationalArithmetic.Word.length]
  omega

/-- Arithmetic plus real scratch clearing: the output tapes remain as a frame.
The cost includes all 67 scratch stacks, even when a primitive leaves garbage. -/
theorem binary_rational_multiplication_with_cleanup (p q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticMultiplier.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      let final := BinaryRationalArithmeticMultiplier.advance steps s
      final.phase = .halt ∧ (BinaryRationalArithmeticMultiplier.output final).value = p*q ∧
      (∀ i, (BinaryWorkspaceCleanup.advance fuel
        (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch final))).tapes i = []) ∧
      BinaryRationalArithmeticMultiplier.bitSteps steps s +
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch final)) ≤
          100000 * (rationalEncodingLength p + rationalEncodingLength q + 1)^3 := by
  obtain ⟨steps, hhalt, hval, _, _, _, hcost⟩ :=
    BinaryRationalArithmeticMultiplier.binary_rational_multiplication_machine p q
  let s := BinaryRationalArithmeticMultiplier.initial
    (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel, hclear, hcleanCost⟩ := rationalMultiplier_cleanup_cost steps s
  refine ⟨steps, fuel, hhalt, hval, hclear, ?_⟩
  have hinit := rationalMultiplier_initial_cells (BinaryRationalArithmetic.encode p)
    (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length, BinaryRationalArithmetic.encode_length] at hinit
  change rationalMultiplierCells s + 2 = _ at hinit
  change BinaryRationalArithmeticMultiplier.bitSteps steps s ≤ _ at hcost
  change BinaryRationalArithmeticMultiplier.bitSteps steps s +
    BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial
      (rationalMultiplierScratch (BinaryRationalArithmeticMultiplier.advance steps s))) ≤ _
  let S := rationalEncodingLength p + rationalEncodingLength q + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
  change _ ≤ 100000*S^3
  change BinaryRationalArithmeticMultiplier.bitSteps steps s ≤ 20000*S^3 at hcost
  have hinitS : rationalMultiplierCells s ≤ S := by dsimp [S]; omega
  nlinarith only [hcleanCost, hcost, hinitS, hcube, hS]

end IdentityTesting.BinaryWorkspaceAdapters
