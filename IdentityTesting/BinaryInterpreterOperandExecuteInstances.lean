import IdentityTesting.BinaryInterpreterOperandExecuteRuns
import IdentityTesting.BinaryInterpreterArithmeticStorage

namespace IdentityTesting.BinaryInterpreterStorage
open BinaryInterpreterLayout RationalComputation
variable {L : Layout}

theorem encoded_initial_cells (W : Storage L) (p q : ℚ) :
    W.cells (L.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) ≤
      rationalEncodingLength p+rationalEncodingLength q := by
  let e := BinaryInterpreterArithmetic.emptyWord
  have hx := W.input_cells false (L.initial e e) (BinaryRationalArithmetic.encode p)
  have hy := W.input_cells true (L.initial (BinaryRationalArithmetic.encode p) e) (BinaryRationalArithmetic.encode q)
  simp only [L.setInput_initial, L.input_initial, Bool.false_eq_true, if_false, if_true] at hx hy
  have hzero : W.cells (L.initial e e) = 0 := W.initial_cells
  rw [hzero] at hx
  have hp := BinaryRationalArithmetic.encode_length p
  have hq := BinaryRationalArithmetic.encode_length q
  change 1 + (BinaryRationalArithmetic.encode p).numerator.magnitude.length +
    (BinaryRationalArithmetic.encode p).denominator.length = rationalEncodingLength p at hp
  change 1 + (BinaryRationalArithmetic.encode q).numerator.magnitude.length +
    (BinaryRationalArithmetic.encode q).denominator.length = rationalEncodingLength q at hq
  simp only [e, BinaryInterpreterArithmetic.emptyWord, List.length_nil] at hx hy
  omega

end IdentityTesting.BinaryInterpreterStorage

namespace IdentityTesting.BinaryInterpreterOperandExecute
open BinaryInterpreterArithmetic BinaryInterpreterStorage BinaryRegisterMachine BinaryRationalRegisters RationalComputation

/-- All six concrete operations consume both encoded operands, execute, write
back, and physically clear the arithmetic and I/O stacks. The operation and
unary destination are provided at entry; decoding those fields is not claimed. -/
theorem binary_operand_execution (op : RationalOp) (s : RationalRegisters) (lhs rhs : RationalOperand)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length) (dst : ℕ) (hd : dst < s.length)
    (code history : List Symbol) :
    ∃ n,
      let W := arithmeticStorage op
      let start := initial W (tape s) (List.replicate dst false)
        (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history
      Finished W s lhs rhs dst (op.eval (lhs.read s) (rhs.read s)) code history (advance W n start) ∧
      bitSteps W n start ≤ 5000*(rationalRegisterEncoding s+s.length+lhs.slots+rhs.slots)+
        100000000*(rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1)^3 := by
  obtain ⟨nm, hm, hz, hcost⟩ := actual_local_run op (lhs.read s) (rhs.read s)
  obtain ⟨n, hrun, hc⟩ := execute_operands (arithmeticStorage op) (arithmeticInputLocal op)
    s lhs rhs hl hr dst hd code history nm (op.eval (lhs.read s) (rhs.read s)) hm hz
  refine ⟨n, hrun, ?_⟩
  have hcells := encoded_initial_cells (arithmeticStorage op) (lhs.read s) (rhs.read s)
  have hcount := arithmeticStorage_count op
  have hout := RationalCall.result_encoding_le ⟨op, lhs.read s, rhs.read s⟩
    (rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s))
    (by change rationalEncodingLength (lhs.read s) ≤ _; omega)
    (by change rationalEncodingLength (rhs.read s) ≤ _; omega)
  change rationalEncodingLength (op.eval (lhs.read s) (rhs.read s)) ≤
    4*(rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s))+3 at hout
  let S := rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hcube : S ≤ S^3 := by
    nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
  have hsum : rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1 = S := rfl
  change (arithmeticLayout op).bitSteps nm ((arithmeticLayout op).initial
    (BinaryRationalArithmetic.encode (lhs.read s)) (BinaryRationalArithmetic.encode (rhs.read s))) ≤ 5500000*S^3 at hcost
  change _ ≤ 5000*(rationalRegisterEncoding s+s.length+lhs.slots+rhs.slots)+100000000*S^3
  nlinarith only [hc, hcost, hcells, hcount, hout, hS, hcube, hsum]

end IdentityTesting.BinaryInterpreterOperandExecute
