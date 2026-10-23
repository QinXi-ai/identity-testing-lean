import IdentityTesting.BinaryWorkspaceRationalSubtractor
import IdentityTesting.BinaryRationalArithmeticComparison

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation
open scoped BigOperators

def rationalComparisonCells (s : BinaryRationalArithmeticComparison.State) : ℕ :=
  rationalSubtractorCells s.core+s.numerator.length+s.denominator.length

def rationalComparisonScratch (s : BinaryRationalArithmeticComparison.State) : Fin 94 → List Bool :=
  Fin.cases (BinaryRationalArithmeticSubtractor.output s.core).numerator.magnitude
    (Fin.cases (BinaryRationalArithmeticSubtractor.output s.core).denominator
      (rationalSubtractorScratch s.core))

theorem rationalComparisonScratch_cells (s : BinaryRationalArithmeticComparison.State) :
    (∑ i, (rationalComparisonScratch s i).length)+s.numerator.length+s.denominator.length =
      rationalComparisonCells s := by
  have h := rationalSubtractorScratch_cells s.core
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  change (BinaryRationalArithmeticSubtractor.output s.core).numerator.magnitude.length +
    ((BinaryRationalArithmeticSubtractor.output s.core).denominator.length+
      ∑ i,(rationalSubtractorScratch s.core i).length)+s.numerator.length+s.denominator.length = _
  dsimp only [rationalComparisonCells]
  omega

theorem rationalComparison_step_cells_cost (s : BinaryRationalArithmeticComparison.State) :
    rationalComparisonCells (BinaryRationalArithmeticComparison.step s) ≤ rationalComparisonCells s+
      (BinaryRationalArithmeticComparison.transitionTrace s).length := by
  have hg := rationalSubtractor_step_cells_cost s.core
  cases hp:s.phase <;> simp only [BinaryRationalArithmeticComparison.step,
    BinaryRationalArithmeticComparison.transitionTrace,hp]
  all_goals (repeat' first | split | simp_all [rationalComparisonCells] | omega)

theorem rationalComparison_cells_cost (n : ℕ) (s : BinaryRationalArithmeticComparison.State) :
    rationalComparisonCells (BinaryRationalArithmeticComparison.advance n s) ≤ rationalComparisonCells s+
      BinaryRationalArithmeticComparison.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticComparison.advance,BinaryRationalArithmeticComparison.bitSteps]
  | succ n ih =>
      have hi := ih (BinaryRationalArithmeticComparison.step s)
      have hs := rationalComparison_step_cells_cost s
      simp only [BinaryRationalArithmeticComparison.advance,BinaryRationalArithmeticComparison.bitSteps]
      omega

end IdentityTesting.BinaryWorkspaceAdapters
