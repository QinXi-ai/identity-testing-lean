import IdentityTesting.BinaryInterpreterMultiplyRuns

namespace IdentityTesting.BinaryInterpreterMultiply
open BinaryRationalRegisters RationalComputation

def CleanIO (s : State) : Prop :=
  s.leftAddress = [] ∧ s.rightAddress = [] ∧ s.destination = [] ∧
  s.saved = [] ∧ s.copyTemp = [] ∧ s.record = [] ∧ s.numWork = [] ∧ s.denWork = []

theorem binary_rational_register_multiply (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := initial (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape (s.set dst (s[a]*s[b])) ∧
      CleanIO (advance n start) ∧
      bitSteps n start ≤ 150*(rationalRegisterEncoding s+s.length) +
        100000*(rationalEncodingLength s[a]+rationalEncodingLength s[b]+1)^3 := by
  obtain ⟨na, hna, hea⟩ := BinaryInterpreterCopy.load_steps s a ha
  obtain ⟨nb, hnb, heb⟩ := BinaryInterpreterCopy.load_steps s b hb
  obtain ⟨nw, hnw, hew⟩ := BinaryInterpreterCopy.store_steps s dst hd (s[a]*s[b])
  obtain ⟨nm, hm, hv, hnum, hden, hzero, hmcost⟩ :=
    BinaryRationalArithmeticMultiplier.binary_rational_multiplication_machine s[a] s[b]
  let c := BinaryRationalArithmeticMultiplier.initial (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b])
  let cf := BinaryRationalArithmeticMultiplier.advance nm c
  have henc : BinaryRationalArithmeticMultiplier.output cf = BinaryRationalArithmetic.encode (s[a]*s[b]) :=
    BinaryRationalArithmetic.canonical_word_eq_encode _ _ hv hnum hden hzero
  obtain ⟨ka, hka, haRun⟩ := forward_left
    (BinaryInterpreterRead.initial (tape s) (List.replicate a false)) na (tape s)
    (BinaryRationalArithmetic.encode s[a]) (List.replicate b false) (List.replicate dst false) hea
  obtain ⟨kb, hkb, hbRun⟩ := forward_right
    (BinaryInterpreterRead.initial (tape s) (List.replicate b false)) nb (tape s)
    (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b]) (List.replicate dst false) heb
  obtain ⟨km, hkm, hmRun, hmCost⟩ := forward_multiply c nm (tape s) (List.replicate dst false) hm
  change advance km (multiplyingState c (tape s) (List.replicate dst false)) =
    storingState cf (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false)
      (BinaryRationalArithmeticMultiplier.output cf)) at hmRun
  rw [henc] at hmRun
  obtain ⟨kw, hkw, hwRun⟩ := forward_store cf
    (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (BinaryRationalArithmetic.encode (s[a]*s[b])))
    nw (tape (s.set dst (s[a]*s[b]))) (BinaryRationalArithmetic.encode (s[a]*s[b])).numerator.negative hew
  let start := initial (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
  change advance ka start = _ at haRun
  change advance kb _ = multiplyingState c (tape s) (List.replicate dst false) at hbRun
  have htotal : advance (ka+(kb+(km+kw))) start =
      {storingState cf (BinaryInterpreterWrite.haltState
        (BinaryRationalArithmetic.encode (s[a]*s[b])).numerator.negative (tape (s.set dst (s[a]*s[b]))))
        with phase := .halt} := by
    rw [advance_add, haRun, advance_add, hbRun, advance_add, hmRun, hwRun]
  refine ⟨ka+(kb+(km+kw)), ?_, ?_, ?_, ?_⟩
  · change (advance _ start).phase = _
    rw [htotal]
  · change (advance _ start).tape = _
    rw [htotal]
    rfl
  · change CleanIO (advance _ start)
    rw [htotal]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change bitSteps (ka+(kb+(km+kw))) start ≤ _
    rw [bitSteps_add, haRun, bitSteps_add, hbRun, bitSteps_add, hmRun]
    have hca := bitSteps_le ka start
    have hcb := bitSteps_le kb (rightState (BinaryInterpreterRead.initial (tape s) (List.replicate b false))
      (BinaryRationalArithmetic.encode s[a]) (List.replicate dst false))
    have hcw := bitSteps_le kw (storingState cf (BinaryInterpreterWrite.initial (tape s)
      (List.replicate dst false) (BinaryRationalArithmetic.encode (s[a]*s[b]))))
    have hout := rational_mul_encoding s[a] s[b]
    rw [tape_length] at hna hnb hnw
    let S := rationalEncodingLength s[a]+rationalEncodingLength s[b]+1
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hcube : S ≤ S^3 := by
      nlinarith only [Nat.mul_le_mul_left (S*S) hS, Nat.mul_le_mul_left S hS]
    change BinaryRationalArithmeticMultiplier.bitSteps nm c ≤ 20000*S^3 at hmcost
    change _ ≤ 150*(rationalRegisterEncoding s+s.length)+100000*S^3
    have hsum : rationalEncodingLength s[a]+rationalEncodingLength s[b]+1 = S := rfl
    nlinarith only [hca, hcb, hcw, hmCost, hmcost, hna, hnb, hnw, hka, hkb, hkw, hout, hS, hcube, hsum]

def multiplyInstruction (a b dst : ℕ) : RationalInstruction := ⟨dst, .mul, .reg a, .reg b⟩

theorem multiplyInstruction_exec (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) :
    (multiplyInstruction a b dst).exec s = s.set dst (s[a]*s[b]) := by
  simp [multiplyInstruction, RationalInstruction.exec, RationalInstruction.call,
    RationalCall.result, RationalOp.eval, RationalOperand.read,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

theorem binary_multiply_instruction (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := initial (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape ((multiplyInstruction a b dst).exec s) ∧
      bitSteps n start ≤ 150*(rationalRegisterEncoding s+s.length) +
        100000*(rationalEncodingLength s[a]+rationalEncodingLength s[b]+1)^3 := by
  rw [multiplyInstruction_exec s a b dst ha hb]
  obtain ⟨n, hh, ht, _, hc⟩ := binary_rational_register_multiply s a b dst ha hb hd
  exact ⟨n, hh, ht, hc⟩

end IdentityTesting.BinaryInterpreterMultiply
