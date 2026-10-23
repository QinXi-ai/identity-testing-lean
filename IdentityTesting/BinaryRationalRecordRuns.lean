import IdentityTesting.BinaryRationalRecordMachine

namespace IdentityTesting.BinaryRationalRecordMachine
open BinaryRationalRegisters

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 7 := by
  unfold transitionTrace
  split <;> (repeat' first | split | decide)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

def splitFuel (w : BinaryRationalArithmetic.Word) : ℕ :=
  1 + ((w.numerator.magnitude.length+1) + ((w.denominator.length+1) +
    ((w.numerator.magnitude.reverse.length+1) + (w.denominator.reverse.length+1))))

theorem split_run (w : BinaryRationalArithmetic.Word) :
    advance (splitFuel w) (initial (wordCells w)) =
      haltState w.numerator.negative w.numerator.magnitude w.denominator := by
  unfold splitFuel
  rw [advance_add]
  change advance ((w.numerator.magnitude.length+1) + ((w.denominator.length+1) +
    ((w.numerator.magnitude.reverse.length+1) + (w.denominator.reverse.length+1))))
    (numState (w.numerator.magnitude.map BinaryRegisterMachine.Cell.bit ++
      .component :: w.denominator.map BinaryRegisterMachine.Cell.bit) w.numerator.negative [] [] [] []) = _
  rw [advance_add, numerator_run]
  simp only [List.append_nil]
  rw [advance_add, denominator_run]
  simp only [List.append_nil]
  rw [advance_add, reverseNum_run]
  simp only [List.reverse_reverse, List.append_nil]
  rw [reverseDen_run]
  simp

theorem splitFuel_eq (w : BinaryRationalArithmetic.Word) : splitFuel w = 2*w.length+3 := by
  simp [splitFuel, BinaryRationalArithmetic.Word.length]
  omega

/-- Actual parsing consumes the symbol record into two canonical-order Bool
stacks. Both temporary reversal stacks are empty. -/
theorem binary_rational_record_split (w : BinaryRationalArithmetic.Word) :
    ∃ fuel, advance fuel (initial (wordCells w)) =
      haltState w.numerator.negative w.numerator.magnitude w.denominator ∧
      output (advance fuel (initial (wordCells w))) = w ∧
      bitSteps fuel (initial (wordCells w)) ≤ 14*w.length+21 := by
  refine ⟨splitFuel w, split_run w, ?_, ?_⟩
  · rw [split_run]
    rfl
  · have h := bitSteps_le (splitFuel w) (initial (wordCells w))
    rw [splitFuel_eq] at h ⊢
    omega

end IdentityTesting.BinaryRationalRecordMachine
