import IdentityTesting.BinaryInterpreterArithmeticBound
import IdentityTesting.BinaryInterpreterCopyLayout
import IdentityTesting.BinaryInterpreterAdditionLayout
import IdentityTesting.BinaryInterpreterSubtractionLayout
import IdentityTesting.BinaryInterpreterMultiplicationLayout
import IdentityTesting.BinaryInterpreterDivisionLayout
import IdentityTesting.BinaryInterpreterComparisonLayout
import IdentityTesting.RationalInstructionTraceStateBounds

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout BinaryInterpreterLayouts BinaryRationalRegisters RationalComputation

def arithmeticLayout : RationalOp → Layout
  | .copy => copying
  | .add => addition
  | .sub => subtraction
  | .mul => multiplication
  | .div => division
  | .le => comparison

/-- Each branch invokes an already proved finite-control arithmetic machine.
There are no arithmetic-correctness fields in the structural Layout interface. -/
theorem actual_local_run (op : RationalOp) (p q : ℚ) :
    ∃ n,
      let L := arithmeticLayout op
      let c := L.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      L.halted (L.advance n c) = true ∧
      L.output (L.advance n c) = BinaryRationalArithmetic.encode (op.eval p q) ∧
      L.bitSteps n c ≤ 5500000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  cases op with
  | copy =>
    refine ⟨1, rfl, rfl, ?_⟩
    change 1 ≤ 5500000*(rationalEncodingLength p+rationalEncodingLength q+1)^3
    have h : 0 < (rationalEncodingLength p+rationalEncodingLength q+1)^3 := by positivity
    omega
  | add =>
    obtain ⟨n, hh, hv, hn, hd, hz, hc⟩ := BinaryRationalArithmeticAdder.binary_rational_addition_machine p q
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [arithmeticLayout, addition_advance]
      change decide ((BinaryRationalArithmeticAdder.advance n (BinaryRationalArithmeticAdder.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))).phase = .halt) = true
      simpa only [decide_eq_true_eq] using hh
    · change BinaryRationalArithmeticAdder.output (addition.advance n _) = _
      rw [addition_advance]
      exact BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hn hd hz
    · change addition.bitSteps n _ ≤ _
      rw [addition_bitSteps]
      change BinaryRationalArithmeticAdder.bitSteps n (BinaryRationalArithmeticAdder.initial
        (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) ≤ _
      omega
  | sub =>
    obtain ⟨n, hh, hv, hn, hd, hz, hc⟩ := BinaryRationalArithmeticSubtractor.binary_rational_subtraction_machine p q
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [arithmeticLayout, subtraction_advance]
      change decide ((BinaryRationalArithmeticSubtractor.advance n (BinaryRationalArithmeticSubtractor.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))).phase = .halt) = true
      simpa only [decide_eq_true_eq] using hh
    · change BinaryRationalArithmeticSubtractor.output (subtraction.advance n _) = _
      rw [subtraction_advance]
      exact BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hn hd hz
    · change subtraction.bitSteps n _ ≤ _
      rw [subtraction_bitSteps]
      change BinaryRationalArithmeticSubtractor.bitSteps n (BinaryRationalArithmeticSubtractor.initial
        (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) ≤ _
      omega
  | mul =>
    obtain ⟨n, hh, hv, hn, hd, hz, hc⟩ := BinaryRationalArithmeticMultiplier.binary_rational_multiplication_machine p q
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [arithmeticLayout, multiplication_advance]
      change decide ((BinaryRationalArithmeticMultiplier.advance n (BinaryRationalArithmeticMultiplier.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))).phase = .halt) = true
      simpa only [decide_eq_true_eq] using hh
    · change BinaryRationalArithmeticMultiplier.output (multiplication.advance n _) = _
      rw [multiplication_advance]
      exact BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hn hd hz
    · change multiplication.bitSteps n _ ≤ _
      rw [multiplication_bitSteps]
      change BinaryRationalArithmeticMultiplier.bitSteps n (BinaryRationalArithmeticMultiplier.initial
        (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) ≤ _
      omega
  | div =>
    obtain ⟨n, hh, hv, hn, hd, hz, hc⟩ := BinaryRationalArithmeticDivider.binary_rational_division_machine p q
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [arithmeticLayout, division_advance]
      change decide ((BinaryRationalArithmeticDivider.advance n (BinaryRationalArithmeticDivider.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))).phase = .halt ∨ (BinaryRationalArithmeticDivider.advance n (BinaryRationalArithmeticDivider.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))).phase = .zeroHalt) = true
      simpa only [decide_eq_true_eq] using hh
    · change BinaryRationalArithmeticDivider.output (division.advance n _) = _
      rw [division_advance]
      exact BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hn hd hz
    · change division.bitSteps n _ ≤ _
      rw [division_bitSteps]
      change BinaryRationalArithmeticDivider.bitSteps n (BinaryRationalArithmeticDivider.initial
        (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) ≤ _
      omega
  | le =>
    obtain ⟨n, hh, he, hc⟩ := BinaryRationalArithmeticComparison.binary_rational_comparison_machine p q
    refine ⟨n, ?_, ?_, ?_⟩
    · simp only [arithmeticLayout, comparison_advance]
      change decide ((BinaryRationalArithmeticComparison.advance n
        (BinaryRationalArithmeticComparison.initial (BinaryRationalArithmetic.encode p)
          (BinaryRationalArithmetic.encode q))).phase = .halt) = true
      simpa only [decide_eq_true_eq] using hh
    · change BinaryRationalArithmeticComparison.output (comparison.advance n _) = _
      rw [comparison_advance]
      exact he
    · change comparison.bitSteps n _ ≤ _
      rw [comparison_bitSteps]
      exact hc

def registerInstruction (op : RationalOp) (a b dst : ℕ) : RationalInstruction :=
  ⟨dst,op,.reg a,.reg b⟩

theorem registerInstruction_exec (op : RationalOp) (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) :
    (registerInstruction op a b dst).exec s = s.set dst (op.eval s[a] s[b]) := by
  simp [registerInstruction, RationalInstruction.exec, RationalInstruction.call,
    RationalCall.result, RationalOperand.read, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- All six rational register operations, executed by the same shared
load-operate-store machine and their concrete finite-control primitive. -/
theorem binary_register_instruction (op : RationalOp) (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := initial (arithmeticLayout op) (tape s)
        (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape ((registerInstruction op a b dst).exec s) ∧
      CleanIO (advance n start) ∧
      bitSteps n start ≤ 300*(rationalRegisterEncoding s+s.length) +
        12000000*(rationalEncodingLength s[a]+rationalEncodingLength s[b]+1)^3 := by
  obtain ⟨nm, hm, hz, hcost⟩ := actual_local_run op s[a] s[b]
  obtain ⟨n, hh, ht, hi, hc⟩ := load_operate_store (arithmeticLayout op) s a b dst ha hb hd
    nm (op.eval s[a] s[b]) hm hz
  refine ⟨n, hh, ?_, hi, ?_⟩
  · rw [registerInstruction_exec op s a b dst ha hb]
    exact ht
  · have hout := RationalCall.result_encoding_le ⟨op,s[a],s[b]⟩
      (rationalEncodingLength s[a]+rationalEncodingLength s[b])
      (by change rationalEncodingLength s[a] ≤ _; omega)
      (by change rationalEncodingLength s[b] ≤ _; omega)
    change rationalEncodingLength (op.eval s[a] s[b]) ≤
      4*(rationalEncodingLength s[a]+rationalEncodingLength s[b])+3 at hout
    let S := rationalEncodingLength s[a]+rationalEncodingLength s[b]+1
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hcube : S ≤ S^3 := by
      nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
    have hsum : rationalEncodingLength s[a]+rationalEncodingLength s[b]+1 = S := rfl
    change _ ≤ 300*(rationalRegisterEncoding s+s.length)+12000000*S^3
    change (arithmeticLayout op).bitSteps nm ((arithmeticLayout op).initial
      (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b])) ≤ 5500000*S^3 at hcost
    nlinarith only [hc,hcost,hout,hS,hcube,hsum]

end IdentityTesting.BinaryInterpreterArithmetic
