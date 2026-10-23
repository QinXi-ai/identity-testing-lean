import IdentityTesting.BinaryRegisterWriteRuns
import IdentityTesting.BinaryRationalArithmeticWords
import IdentityTesting.RationalInstructionTrace

namespace IdentityTesting.BinaryRationalRegisters
open BinaryRegisterMachine RationalComputation

/-- Sign, numerator bits, a component delimiter, and denominator bits. -/
def wordCells (w : BinaryRationalArithmetic.Word) : List Cell :=
  Cell.bit w.numerator.negative ::
    (w.numerator.magnitude.map Cell.bit ++ Cell.component :: w.denominator.map Cell.bit)

def rationalCells (q : ℚ) : List Cell := wordCells (BinaryRationalArithmetic.encode q)
def records (s : RationalRegisters) : List (List Cell) := s.map rationalCells
def tape (s : RationalRegisters) : List Symbol := BinaryRegisterMachine.encode (records s)

theorem wordCells_length (w : BinaryRationalArithmetic.Word) :
    (wordCells w).length = w.length + 1 := by
  simp [wordCells, BinaryRationalArithmetic.Word.length]
  omega

theorem rationalCells_length (q : ℚ) :
    (rationalCells q).length = rationalEncodingLength q + 1 := by
  rw [rationalCells, wordCells_length, BinaryRationalArithmetic.encode_length]

theorem tape_length (s : RationalRegisters) :
    (tape s).length = rationalRegisterEncoding s + s.length := by
  induction s with
  | nil => rfl
  | cons q s ih =>
    simp only [tape, records, List.map_cons, encode, List.length_append,
      List.length_map, List.length_cons, rationalCells_length] at ih ⊢
    simp only [rationalRegisterEncoding, List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem records_decomposition (s : RationalRegisters) (i : ℕ) (hi : i < s.length) :
    records s = records (s.take i) ++ rationalCells s[i] :: records (s.drop (i+1)) := by
  have hs : s = s.take i ++ s[i] :: s.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [hs]
  simp only [records, List.map_append, List.map_cons]

theorem binary_rational_register_read (s : RationalRegisters) (i : ℕ) (hi : i < s.length) :
    ∃ fuel, BinaryRegisterMachine.advance fuel
      (seekState (tape s) (List.replicate i false) []) = haltState (tape s) (rationalCells s[i]) ∧
      BinaryRegisterMachine.bitSteps fuel (seekState (tape s) (List.replicate i false) []) ≤
        39 * (rationalRegisterEncoding s + s.length) + 52 := by
  have h := binary_register_read (records (s.take i)) (records (s.drop (i+1))) (rationalCells s[i])
  have hlen : (records (s.take i)).length = i := by simp [records, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← records_decomposition s i hi, ← tape, hlen, tape_length] at h
  exact h

theorem records_set (s : RationalRegisters) (i : ℕ) (hi : i < s.length) (q : ℚ) :
    records (s.set i q) = records (s.take i) ++ rationalCells q :: records (s.drop (i+1)) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hi]
  simp only [records, List.map_append, List.map_cons]

theorem binary_rational_register_write (s : RationalRegisters) (i : ℕ) (hi : i < s.length) (q : ℚ) :
    ∃ fuel, BinaryRegisterWriteMachine.advance fuel
      (BinaryRegisterWriteMachine.seekState (tape s) (List.replicate i false) [] (rationalCells q)) =
        BinaryRegisterWriteMachine.haltState (tape (s.set i q)) ∧
      BinaryRegisterWriteMachine.bitSteps fuel
        (BinaryRegisterWriteMachine.seekState (tape s) (List.replicate i false) [] (rationalCells q)) ≤
        24 * (rationalRegisterEncoding s + s.length) + 24 * (rationalEncodingLength q + 1) + 60 := by
  have h := BinaryRegisterWriteMachine.binary_register_write (records (s.take i))
    (records (s.drop (i+1))) (rationalCells s[i]) (rationalCells q)
  have hlen : (records (s.take i)).length = i := by simp [records, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← records_decomposition s i hi, ← records_set s i hi q, ← tape, ← tape,
    hlen, tape_length, rationalCells_length] at h
  exact h

/-- The writeback phase matches the existing instruction interpreter exactly.
The input record here is the arithmetic result; computing it is a separate phase. -/
theorem binary_instruction_writeback (s : RationalRegisters) (i : RationalInstruction)
    (hi : i.dst < s.length) :
    ∃ fuel, BinaryRegisterWriteMachine.advance fuel
      (BinaryRegisterWriteMachine.seekState (tape s) (List.replicate i.dst false) []
        (rationalCells (i.call s).result)) =
        BinaryRegisterWriteMachine.haltState (tape (i.exec s)) ∧
      BinaryRegisterWriteMachine.bitSteps fuel
        (BinaryRegisterWriteMachine.seekState (tape s) (List.replicate i.dst false) []
          (rationalCells (i.call s).result)) ≤
        24 * (rationalRegisterEncoding s + s.length) +
          24 * (rationalEncodingLength (i.call s).result + 1) + 60 := by
  exact binary_rational_register_write s i.dst hi (i.call s).result

end IdentityTesting.BinaryRationalRegisters
