import IdentityTesting.BinaryInterpreterStorage
import IdentityTesting.BinaryInterpreterCopyLayout
import IdentityTesting.BinaryInterpreterMultiplicationLayout
import IdentityTesting.BinaryMultiplierStorage

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterStorage BinaryWorkspaceAdapters BinaryWorkspaceGrowth
open scoped BigOperators

def copyCells (c : CopyCore) : ℕ :=
  c.left.numerator.magnitude.length+c.left.denominator.length+
    c.right.numerator.magnitude.length+c.right.denominator.length
def copyTapes (c : CopyCore) : Fin 4 → List Bool :=
  ![c.left.numerator.magnitude,c.left.denominator,c.right.numerator.magnitude,c.right.denominator]
def copySetTapes (c : CopyCore) (f : Fin 4 → List Bool) : CopyCore :=
  {c with left := ⟨⟨c.left.numerator.negative,f 0⟩,f 1⟩, right := ⟨⟨c.right.numerator.negative,f 2⟩,f 3⟩}

def copyStorage : Storage copying where
  count := 4
  cells := copyCells
  tapes := copyTapes
  setTapes := copySetTapes
  tapes_set := by intro c f; funext i; fin_cases i <;> rfl
  set_tapes := by intro c; rfl
  tapes_cells := by intro c; simp [copyTapes,copyCells,Fin.sum_univ_succ]; omega
  initial_cells := rfl
  input_cells := by intro right c w; cases right <;> simp [copying,copySetInput,copyInput,copyCells] <;> omega
  output_cells := by intro c n d; simp [copying,copySetOutput,copyCells]; omega
  step_cells_cost := by intro c; simp [copying,copyStep,copyCells]

def multiplicationStorage : Storage multiplication where
  count := 69
  cells := rationalMultiplierCells
  tapes := BinaryMultiplierStorage.tapes
  setTapes := BinaryMultiplierStorage.setTapes
  tapes_set := BinaryMultiplierStorage.tapes_set
  set_tapes := BinaryMultiplierStorage.set_tapes
  tapes_cells := BinaryMultiplierStorage.tapes_cells
  initial_cells := rfl
  input_cells := by
    intro right c w
    cases right <;> simp [multiplication,mulSetInput,mulInput,rationalMultiplierCells,
      signedMultiplierCells,multiplierCells] <;> omega
  output_cells := by
    intro c n d
    simp [multiplication,mulSetOutput,BinaryRationalArithmeticMultiplier.output,
      rationalMultiplierCells,rationalNormalizationCells,divisionCells,normalizerCells]
    omega
  step_cells_cost := rationalMultiplier_step_cells_cost

end IdentityTesting.BinaryInterpreterLayouts
