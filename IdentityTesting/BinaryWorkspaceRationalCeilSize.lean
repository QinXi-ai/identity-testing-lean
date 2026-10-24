import IdentityTesting.BinaryWorkspaceCost
import IdentityTesting.BinaryRationalArithmeticCeilSizeBound

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth RationalComputation
open scoped BigOperators

def bitCounterCells (s : BinaryRationalArithmeticBitCounter.State) : ℕ :=
  s.source.length+s.counter.length+s.temp.length

theorem bitCounter_step_cells (s : BinaryRationalArithmeticBitCounter.State) :
    bitCounterCells (BinaryRationalArithmeticBitCounter.step s) ≤ bitCounterCells s+1 := by
  cases hp:s.phase <;> simp only [BinaryRationalArithmeticBitCounter.step,hp]
  all_goals (repeat' first | split | simp_all [bitCounterCells] | omega)

def bitLengthCells (s : BinaryRationalArithmeticBitLength.State) : ℕ :=
  bitCounterCells s.core+normalizerCells s.norm+s.temp.length

theorem bitLength_step_cells (s : BinaryRationalArithmeticBitLength.State) :
    bitLengthCells (BinaryRationalArithmeticBitLength.step s) ≤ bitLengthCells s+1 := by
  have hc := bitCounter_step_cells s.core
  have hn := normalizer_step_cells s.norm
  cases hp:s.phase <;> simp only [BinaryRationalArithmeticBitLength.step,hp]
  all_goals (repeat' first | split | simp_all [bitLengthCells,bitCounterCells,normalizerCells] | omega)

def rationalCeilSizeCells (s : BinaryRationalArithmeticCeilSize.State) : ℕ :=
  divisionCells s.div+bitCounterCells s.counter+normalizerCells s.norm+
    bitLengthCells s.measure+s.temp.length+s.denominator.length

theorem rationalCeilSize_step_cells (s : BinaryRationalArithmeticCeilSize.State) :
    rationalCeilSizeCells (BinaryRationalArithmeticCeilSize.step s) ≤ rationalCeilSizeCells s+1 := by
  have hd := division_step_cells s.div
  have hc := bitCounter_step_cells s.counter
  have hn := normalizer_step_cells s.norm
  have hl := bitLength_step_cells s.measure
  cases hp:s.phase <;> simp only [BinaryRationalArithmeticCeilSize.step,hp]
  all_goals (repeat' first | split | simp_all [rationalCeilSizeCells,divisionCells,bitCounterCells,
    bitLengthCells,normalizerCells] | omega)

theorem rationalCeilSize_step_cells_cost (s : BinaryRationalArithmeticCeilSize.State) :
    rationalCeilSizeCells (BinaryRationalArithmeticCeilSize.step s) ≤ rationalCeilSizeCells s+
      (BinaryRationalArithmeticCeilSize.transitionTrace s).length := by
  have hg := rationalCeilSize_step_cells s
  cases hp:s.phase <;> simp only [BinaryRationalArithmeticCeilSize.transitionTrace,hp]
  all_goals (repeat' first | split | simp_all [BinaryRationalArithmeticCeilSize.step] | omega)

theorem rationalCeilSize_cells_cost (n : ℕ) (s : BinaryRationalArithmeticCeilSize.State) :
    rationalCeilSizeCells (BinaryRationalArithmeticCeilSize.advance n s) ≤ rationalCeilSizeCells s+
      BinaryRationalArithmeticCeilSize.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticCeilSize.advance,BinaryRationalArithmeticCeilSize.bitSteps]
  | succ n ih =>
      have hi := ih (BinaryRationalArithmeticCeilSize.step s)
      have hs := rationalCeilSize_step_cells_cost s
      simp only [BinaryRationalArithmeticCeilSize.advance,BinaryRationalArithmeticCeilSize.bitSteps]
      omega

def rationalCeilSizeScratch (s : BinaryRationalArithmeticCeilSize.State) : Fin 27 → List Bool :=
  ![s.div.source,s.div.bits,s.div.divisor,s.div.temp,
    s.div.sub.left,s.div.sub.right,s.div.sub.work,s.div.sub.out,
    s.div.quot.source,s.div.quot.work,s.div.quot.out,
    s.div.rem.source,s.div.rem.work,s.div.rem.out,
    s.counter.source,s.counter.counter,s.counter.temp,
    s.norm.source,s.norm.work,s.norm.out,
    s.measure.core.source,s.measure.core.counter,s.measure.core.temp,
    s.measure.norm.source,s.measure.norm.work,s.measure.temp,s.temp]

theorem rationalCeilSizeScratch_cells (s : BinaryRationalArithmeticCeilSize.State) :
    (∑ i,(rationalCeilSizeScratch s i).length)+s.measure.norm.out.length+s.denominator.length =
      rationalCeilSizeCells s := by
  simp [rationalCeilSizeScratch,Fin.sum_univ_succ,rationalCeilSizeCells,divisionCells,
    adderCells,normalizerCells,bitCounterCells,bitLengthCells]
  omega

theorem rationalCeilSize_cleanup (s : BinaryRationalArithmeticCeilSize.State) :
    ∃ fuel, (∀ i,(BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch s))).tapes i=[]) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch s)) ≤
        3*(27+rationalCeilSizeCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalCeilSizeScratch s)
  dsimp only at h
  refine ⟨27+∑ i,(rationalCeilSizeScratch s i).length,h.2.1,?_⟩
  have hs := rationalCeilSizeScratch_cells s
  exact h.2.2.trans (Nat.mul_le_mul_left 3 (by omega))

theorem rationalCeilSize_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticCeilSize.State) :
    ∃ fuel, (∀ i,(BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch (BinaryRationalArithmeticCeilSize.advance n s)))).tapes i=[]) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch (BinaryRationalArithmeticCeilSize.advance n s))) ≤
        3*(27+rationalCeilSizeCells s+BinaryRationalArithmeticCeilSize.bitSteps n s) := by
  obtain ⟨fuel,hc,hb⟩ := rationalCeilSize_cleanup (BinaryRationalArithmeticCeilSize.advance n s)
  refine ⟨fuel,hc,?_⟩
  have hg := rationalCeilSize_cells_cost n s
  exact hb.trans (Nat.mul_le_mul_left 3 (by omega))

theorem rationalCeilSize_initial_cells (q : BinaryRationalArithmetic.Word) :
    rationalCeilSizeCells (BinaryRationalArithmeticCeilSize.initial q)+1=q.length := by
  simp [rationalCeilSizeCells,BinaryRationalArithmeticCeilSize.initial,divisionCells,
    BinaryDivisionMachine.initial,BinaryDivisionMachine.word,BinarySubtractorMachine.haltState,BinaryAdderMachine.haltState,
    adderCells,normalizerCells,bitCounterCells,bitLengthCells,BinaryRationalArithmeticBitLength.initial,
    BinaryRationalArithmeticBitCounter.initial,BinaryRationalArithmetic.Word.length]
  omega

theorem binary_rational_ceilSize_with_cleanup (q : ℚ) :
    ∃ steps fuel,
      let s := BinaryRationalArithmeticCeilSize.initial (BinaryRationalArithmetic.encode q)
      let f := BinaryRationalArithmeticCeilSize.advance steps s
      f.phase=.halt ∧ BinaryRationalArithmeticCeilSize.output f=BinaryRationalArithmetic.encode ((Nat.ceil q).size:ℚ) ∧
      (∀ i,(BinaryWorkspaceCleanup.advance fuel (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch f))).tapes i=[]) ∧
      BinaryRationalArithmeticCeilSize.bitSteps steps s+
        BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalCeilSizeScratch f)) ≤
        40000*(rationalEncodingLength q+1)^2 := by
  obtain ⟨steps,hh,ho,hb⟩ := BinaryRationalArithmeticCeilSize.binary_rational_ceilSize_machine q
  let s := BinaryRationalArithmeticCeilSize.initial (BinaryRationalArithmetic.encode q)
  obtain ⟨fuel,hc,hb'⟩ := rationalCeilSize_cleanup_cost steps s
  refine ⟨steps,fuel,hh,ho,hc,?_⟩
  have hi := rationalCeilSize_initial_cells (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length] at hi
  change rationalCeilSizeCells s+1=_ at hi
  change BinaryRationalArithmeticCeilSize.bitSteps steps s ≤ _ at hb
  change BinaryRationalArithmeticCeilSize.bitSteps steps s+_ ≤ _
  nlinarith only [hi,hb,hb']

end IdentityTesting.BinaryWorkspaceAdapters
