import IdentityTesting.BinaryInterpreterCeilSizeLayout
import IdentityTesting.BinaryInterpreterStorage

namespace IdentityTesting.BinaryInterpreterCeilSize
open BinaryInterpreterLayout BinaryInterpreterStorage BinaryWorkspaceAdapters BinaryWorkspaceGrowth
open scoped BigOperators

def cells (c : Core) : ℕ := rationalCeilSizeCells c.machine +
  c.auxiliary.numerator.magnitude.length + c.auxiliary.denominator.length

def tapes (c : Core) : Fin 31 → List Bool :=
  ![c.machine.div.source, c.machine.div.bits, c.machine.div.divisor, c.machine.div.temp,
    c.machine.div.sub.left, c.machine.div.sub.right, c.machine.div.sub.work, c.machine.div.sub.out,
    c.machine.div.quot.source, c.machine.div.quot.work, c.machine.div.quot.out,
    c.machine.div.rem.source, c.machine.div.rem.work, c.machine.div.rem.out,
    c.machine.counter.source, c.machine.counter.counter, c.machine.counter.temp,
    c.machine.norm.source, c.machine.norm.work, c.machine.norm.out,
    c.machine.measure.core.source, c.machine.measure.core.counter, c.machine.measure.core.temp,
    c.machine.measure.norm.source, c.machine.measure.norm.work, c.machine.measure.temp, c.machine.temp,
    c.machine.measure.norm.out, c.machine.denominator,
    c.auxiliary.numerator.magnitude, c.auxiliary.denominator]

def setTapes (c : Core) (f : Fin 31 → List Bool) : Core :=
  { c with
    machine := { c.machine with
      div := { c.machine.div with
        source := f 0
        bits := f 1
        divisor := f 2
        temp := f 3
        sub := {c.machine.div.sub with left := f 4, right := f 5, work := f 6, out := f 7}
        quot := {c.machine.div.quot with source := f 8, work := f 9, out := f 10}
        rem := {c.machine.div.rem with source := f 11, work := f 12, out := f 13} }
      counter := {c.machine.counter with source := f 14, counter := f 15, temp := f 16}
      norm := {c.machine.norm with source := f 17, work := f 18, out := f 19}
      measure := { c.machine.measure with
        core := {c.machine.measure.core with source := f 20, counter := f 21, temp := f 22}
        norm := {c.machine.measure.norm with source := f 23, work := f 24, out := f 27}
        temp := f 25 }
      temp := f 26
      denominator := f 28 }
    auxiliary := ⟨⟨c.auxiliary.numerator.negative, f 29⟩, f 30⟩ }

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def storage : Storage layout where
  count := 31
  cells := cells
  tapes := tapes
  setTapes := setTapes
  tapes_set := by intro c f; funext i; fin_cases i <;> rfl
  set_tapes := by intro c; rfl
  tapes_cells := by
    intro c
    simp [tapes, Fin.sum_univ_succ, cells, rationalCeilSizeCells, divisionCells,
      adderCells, normalizerCells, bitCounterCells, bitLengthCells]
    omega
  initial_cells := by rfl
  input_cells := by
    intro right c w
    cases right <;>
      simp [layout, input, setInput, cells, rationalCeilSizeCells, divisionCells]
    all_goals omega
  output_cells := by
    intro c n d
    simp [layout, setOutput, cells, rationalCeilSizeCells, bitLengthCells,
      normalizerCells, BinaryRationalArithmeticCeilSize.output, BinaryRationalArithmeticBitLength.output]
    omega
  step_cells_cost := by
    intro c
    have h := rationalCeilSize_step_cells_cost c.machine
    change rationalCeilSizeCells (BinaryRationalArithmeticCeilSize.step c.machine) +
      c.auxiliary.numerator.magnitude.length + c.auxiliary.denominator.length ≤
      rationalCeilSizeCells c.machine + c.auxiliary.numerator.magnitude.length +
      c.auxiliary.denominator.length + (BinaryRationalArithmeticCeilSize.transitionTrace c.machine).length
    omega

end IdentityTesting.BinaryInterpreterCeilSize
