import IdentityTesting.BinaryInterpreterBasicStorage
import IdentityTesting.BinaryInterpreterAdditionLayout
import IdentityTesting.BinaryInterpreterSubtractionLayout
import IdentityTesting.BinaryInterpreterDivisionLayout
import IdentityTesting.BinaryInterpreterComparisonLayout
import IdentityTesting.BinaryAdderStorage
import IdentityTesting.BinaryWorkspaceRationalSubtractor
import IdentityTesting.BinaryWorkspaceRationalComparisonCost
import IdentityTesting.BinaryWorkspaceRationalDivider

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterStorage BinaryWorkspaceAdapters BinaryWorkspaceGrowth
open scoped BigOperators
set_option maxRecDepth 4096

def additionStorage : Storage addition where
  count := 94
  cells := rationalAdderCells
  tapes := BinaryAdderStorage.tapes
  setTapes := BinaryAdderStorage.setTapes
  tapes_set := BinaryAdderStorage.tapes_set
  set_tapes := BinaryAdderStorage.set_tapes
  tapes_cells := BinaryAdderStorage.tapes_cells
  initial_cells := rfl
  input_cells := by
    intro right c w
    cases right <;> simp [addition,addSetInput,addInput,rationalAdderCells,rationalMultiplierCells,
      signedMultiplierCells,multiplierCells] <;> omega
  output_cells := by
    intro c n d
    simp [addition,addSetOutput,BinaryRationalArithmeticAdder.output,BinaryRationalArithmeticMultiplier.output,
      rationalAdderCells,rationalMultiplierCells,rationalNormalizationCells,divisionCells,normalizerCells]
    omega
  step_cells_cost := rationalAdder_step_cells_cost

def subtractionStorage : Storage subtraction where
  count := 94
  cells := rationalSubtractorCells
  tapes := fun c => BinaryAdderStorage.tapes c.core
  setTapes := fun c f => {c with core := BinaryAdderStorage.setTapes c.core f}
  tapes_set := by intro c f; exact BinaryAdderStorage.tapes_set c.core f
  set_tapes := by
    intro c
    simp only [BinaryAdderStorage.set_tapes]
    cases c
    rfl
  tapes_cells := by intro c; exact BinaryAdderStorage.tapes_cells c.core
  initial_cells := rfl
  input_cells := by intro right c w; exact additionStorage.input_cells right c.core w
  output_cells := by intro c n d; exact additionStorage.output_cells c.core n d
  step_cells_cost := rationalSubtractor_step_cells_cost

def divTapes (c : BinaryRationalArithmeticDivider.State) : Fin 70 → List Bool :=
  Fin.cases c.zeroDen (BinaryMultiplierStorage.tapes c.core)
def divSetTapes (c : BinaryRationalArithmeticDivider.State) (f : Fin 70 → List Bool) :
    BinaryRationalArithmeticDivider.State :=
  {c with zeroDen := f 0, core := BinaryMultiplierStorage.setTapes c.core (fun i => f i.succ)}

def divisionStorage : Storage division where
  count := 70
  cells := rationalDividerCells
  tapes := divTapes
  setTapes := divSetTapes
  tapes_set := by
    intro c f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change BinaryMultiplierStorage.tapes (BinaryMultiplierStorage.setTapes c.core (fun j => f j.succ)) j = _
      rw [BinaryMultiplierStorage.tapes_set]
  set_tapes := by
    intro c
    simp [divSetTapes,divTapes,BinaryMultiplierStorage.set_tapes]
    cases c
    rfl
  tapes_cells := by
    intro c
    rw [Fin.sum_univ_succ]
    change c.zeroDen.length+(∑ i,(BinaryMultiplierStorage.tapes c.core i).length) = _
    rw [BinaryMultiplierStorage.tapes_cells]
    simp [rationalDividerCells,Nat.add_comm]
  initial_cells := rfl
  input_cells := by
    intro right c w
    cases right <;> simp [division,divSetInput,divInput,BinaryRationalArithmeticDivider.reciprocalLayout,
      mulSetInput,mulInput,rationalDividerCells,rationalMultiplierCells,signedMultiplierCells,multiplierCells] <;> omega
  output_cells := by
    intro c n d
    by_cases h : c.phase = .zeroHalt <;>
      simp [division,divSetOutput,h,BinaryRationalArithmeticDivider.output,
        BinaryRationalArithmeticMultiplier.output,mulSetOutput,rationalDividerCells,
        rationalMultiplierCells,signedMultiplierCells,multiplierCells,rationalNormalizationCells,
        divisionCells,normalizerCells] <;> omega
  step_cells_cost := rationalDivider_step_cells_cost

def cmpTapes (c : BinaryRationalArithmeticComparison.State) : Fin 96 → List Bool :=
  Fin.cases c.numerator (Fin.cases c.denominator (BinaryAdderStorage.tapes c.core.core))
def cmpSetTapes (c : BinaryRationalArithmeticComparison.State) (f : Fin 96 → List Bool) :
    BinaryRationalArithmeticComparison.State :=
  {c with numerator := f 0, denominator := f 1, core := {c.core with core := BinaryAdderStorage.setTapes c.core.core (fun i => f i.succ.succ)}}

def comparisonStorage : Storage comparison where
  count := 96
  cells := rationalComparisonCells
  tapes := cmpTapes
  setTapes := cmpSetTapes
  tapes_set := by
    intro c f
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · change BinaryAdderStorage.tapes (BinaryAdderStorage.setTapes c.core.core (fun k => f k.succ.succ)) k = _
        rw [BinaryAdderStorage.tapes_set]
  set_tapes := by
    intro c
    change {c with numerator := c.numerator, denominator := c.denominator, core := {c.core with core := BinaryAdderStorage.setTapes c.core.core (BinaryAdderStorage.tapes c.core.core)}} = c
    rw [BinaryAdderStorage.set_tapes]
    cases c
    rfl
  tapes_cells := by
    intro c
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    change c.numerator.length+(c.denominator.length+(∑ i,(BinaryAdderStorage.tapes c.core.core i).length)) = _
    rw [BinaryAdderStorage.tapes_cells]
    simp [rationalComparisonCells,rationalSubtractorCells,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  initial_cells := rfl
  input_cells := by
    intro right c w
    have h := subtractionStorage.input_cells right c.core w
    change rationalSubtractorCells (subSetInput right c.core w)+(subInput right c.core).numerator.magnitude.length+
      (subInput right c.core).denominator.length = rationalSubtractorCells c.core+w.numerator.magnitude.length+w.denominator.length at h
    simp only [comparison,cmpSetInput,cmpInput,rationalComparisonCells]
    omega
  output_cells := by
    intro c n d
    simp [comparison,cmpSetOutput,BinaryRationalArithmeticComparison.output,rationalComparisonCells]
    omega
  step_cells_cost := rationalComparison_step_cells_cost

end IdentityTesting.BinaryInterpreterLayouts
