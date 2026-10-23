import IdentityTesting.BinaryWorkspaceAdapters
import IdentityTesting.BinaryRationalNormalizationMachine

namespace IdentityTesting.BinaryWorkspaceGrowth

theorem subtractor_step_cells (s : BinarySubtractorMachine.State) :
    adderCells (BinarySubtractorMachine.step s) ≤ adderCells s + 1 := by
  have h := adder_step_cells s
  cases hp : s.phase <;> simp only [BinarySubtractorMachine.step, hp]
  all_goals first | exact h | simp [adderCells]

def divisionCells (s : BinaryDivisionMachine.State) : ℕ :=
  s.source.length + s.bits.length + s.divisor.length + s.temp.length + adderCells s.sub +
    normalizerCells s.quot + normalizerCells s.rem

theorem division_step_cells (s : BinaryDivisionMachine.State) :
    divisionCells (BinaryDivisionMachine.step s) ≤ divisionCells s + 1 := by
  have hs := subtractor_step_cells s.sub
  have hq := normalizer_step_cells s.quot
  have hr := normalizer_step_cells s.rem
  cases hp : s.phase <;> simp only [BinaryDivisionMachine.step, hp]
  all_goals (repeat' first | split | simp_all [divisionCells, adderCells, normalizerCells] | omega)

def gcdCells (s : BinaryGcdMachine.State) : ℕ := divisionCells s.div + s.temp.length

theorem gcd_step_cells (s : BinaryGcdMachine.State) :
    gcdCells (BinaryGcdMachine.step s) ≤ gcdCells s + 1 := by
  have hd := division_step_cells s.div
  cases hp : s.phase <;> simp only [BinaryGcdMachine.step, hp]
  all_goals (repeat' first | split | simp_all [gcdCells, divisionCells, adderCells, normalizerCells] | omega)

def rationalNormalizationCells (s : BinaryRationalNormalizationMachine.State) : ℕ :=
  gcdCells s.gcd + divisionCells s.num + divisionCells s.den + s.temp.length

theorem rationalNormalization_step_cells (s : BinaryRationalNormalizationMachine.State) :
    rationalNormalizationCells (BinaryRationalNormalizationMachine.step s) ≤ rationalNormalizationCells s + 1 := by
  have hg := gcd_step_cells s.gcd
  have hn := division_step_cells s.num
  have hd := division_step_cells s.den
  cases hp : s.phase <;> simp only [BinaryRationalNormalizationMachine.step, hp]
  all_goals (repeat' first | split | simp_all [rationalNormalizationCells, gcdCells,
    divisionCells, adderCells, normalizerCells] | omega)

theorem rationalNormalization_advance_cells (n : ℕ) (s : BinaryRationalNormalizationMachine.State) :
    rationalNormalizationCells (BinaryRationalNormalizationMachine.advance n s) ≤ rationalNormalizationCells s + n := by
  induction n generalizing s with
  | zero => simp [BinaryRationalNormalizationMachine.advance]
  | succ n ih =>
    have hi := ih (BinaryRationalNormalizationMachine.step s)
    have hs := rationalNormalization_step_cells s
    simp only [BinaryRationalNormalizationMachine.advance]
    omega

end IdentityTesting.BinaryWorkspaceGrowth
