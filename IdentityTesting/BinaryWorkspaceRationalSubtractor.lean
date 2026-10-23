import IdentityTesting.BinaryWorkspaceAdditionBound
import IdentityTesting.BinaryRationalArithmeticSubtractor

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation
open scoped BigOperators

def rationalSubtractorCells (s : BinaryRationalArithmeticSubtractor.State) : ℕ := rationalAdderCells s.core
def rationalSubtractorScratch (s : BinaryRationalArithmeticSubtractor.State) : Fin 92 → List Bool := rationalAdderScratch s.core

theorem rationalSubtractor_step_cells_cost (s : BinaryRationalArithmeticSubtractor.State) :
    rationalSubtractorCells (BinaryRationalArithmeticSubtractor.step s) ≤ rationalSubtractorCells s +
      (BinaryRationalArithmeticSubtractor.transitionTrace s).length := by
  have hg := rationalAdder_step_cells_cost s.core
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticSubtractor.step,
    BinaryRationalArithmeticSubtractor.transitionTrace,hp]
  all_goals (repeat' first | split | simp_all [rationalSubtractorCells,rationalAdderCells,
    signedMultiplierCells,multiplierCells,normalizerCells] | omega)

theorem rationalSubtractor_cells_cost (n : ℕ) (s : BinaryRationalArithmeticSubtractor.State) :
    rationalSubtractorCells (BinaryRationalArithmeticSubtractor.advance n s) ≤ rationalSubtractorCells s +
      BinaryRationalArithmeticSubtractor.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticSubtractor.advance,BinaryRationalArithmeticSubtractor.bitSteps]
  | succ n ih =>
      have hi := ih (BinaryRationalArithmeticSubtractor.step s)
      have hs := rationalSubtractor_step_cells_cost s
      simp only [BinaryRationalArithmeticSubtractor.advance,BinaryRationalArithmeticSubtractor.bitSteps]
      omega

theorem rationalSubtractorScratch_cells (s : BinaryRationalArithmeticSubtractor.State) :
    (∑ i, (rationalSubtractorScratch s i).length) +
      (BinaryRationalArithmeticSubtractor.output s).numerator.magnitude.length +
      (BinaryRationalArithmeticSubtractor.output s).denominator.length = rationalSubtractorCells s :=
  rationalAdderScratch_cells s.core

theorem rationalSubtractor_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticSubtractor.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalSubtractorScratch (BinaryRationalArithmeticSubtractor.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalSubtractorScratch (BinaryRationalArithmeticSubtractor.advance n s))) ≤
        3*(92+rationalSubtractorCells s+BinaryRationalArithmeticSubtractor.bitSteps n s) := by
  obtain ⟨fuel,hc,hb⟩ := rationalAdder_cleanup (BinaryRationalArithmeticSubtractor.advance n s).core
  refine ⟨fuel,hc,?_⟩
  have hg := rationalSubtractor_cells_cost n s
  change BinaryWorkspaceCleanup.bitSteps fuel
    (BinaryWorkspaceCleanup.initial (rationalSubtractorScratch (BinaryRationalArithmeticSubtractor.advance n s))) ≤
      3*(92+rationalSubtractorCells (BinaryRationalArithmeticSubtractor.advance n s)) at hb
  omega

theorem binary_rational_subtraction_with_cleanup (p q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticSubtractor.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      let final := BinaryRationalArithmeticSubtractor.advance steps s
      final.phase = .halt ∧ (BinaryRationalArithmeticSubtractor.output final).value = p-q ∧
      (∀ i, (BinaryWorkspaceCleanup.advance fuel (BinaryWorkspaceCleanup.initial (rationalSubtractorScratch final))).tapes i = []) ∧
      BinaryRationalArithmeticSubtractor.bitSteps steps s +
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalSubtractorScratch final)) ≤
          12000000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  obtain ⟨steps,hh,hv,_,_,_,hb⟩ := BinaryRationalArithmeticSubtractor.binary_rational_subtraction_machine p q
  let s := BinaryRationalArithmeticSubtractor.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel,hc,hb'⟩ := rationalSubtractor_cleanup_cost steps s
  refine ⟨steps,fuel,hh,hv,hc,?_⟩
  have hi := rationalAdder_initial_cells (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length,BinaryRationalArithmetic.encode_length] at hi
  change rationalSubtractorCells s+2 = _ at hi
  change BinaryRationalArithmeticSubtractor.bitSteps steps s ≤ _ at hb
  change BinaryRationalArithmeticSubtractor.bitSteps steps s + _ ≤ _
  let S := rationalEncodingLength p+rationalEncodingLength q+1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS,Nat.mul_le_mul_left S hS]
  have hiS : rationalSubtractorCells s ≤ S := by dsimp [S]; omega
  change _ ≤ 12000000*S^3
  change BinaryRationalArithmeticSubtractor.bitSteps steps s ≤ 2700000*S^3 at hb
  nlinarith only [hb,hb',hiS,hcube,hS]

end IdentityTesting.BinaryWorkspaceAdapters
