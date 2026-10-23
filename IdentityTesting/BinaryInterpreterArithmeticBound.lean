import IdentityTesting.BinaryInterpreterArithmeticRuns

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout BinaryRationalRegisters RationalComputation

def CleanIO {L : Layout} (s : State L) : Prop :=
  s.leftAddress = [] ∧ s.rightAddress = [] ∧ s.destination = [] ∧
  s.saved = [] ∧ s.copyTemp = [] ∧ s.record = [] ∧ s.numWork = [] ∧ s.denWork = []

/-- Simulation of an actual local primitive run, with explicit register load,
store, and finite control costs. Arithmetic correctness is supplied by the
separate theorem for the concrete local machine, rather than by Layout fields. -/
theorem load_operate_store (L : Layout) (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) (nm : ℕ) (z : ℚ)
    (hm : L.halted (L.advance nm (L.initial (BinaryRationalArithmetic.encode s[a])
      (BinaryRationalArithmetic.encode s[b]))) = true)
    (hz : L.output (L.advance nm (L.initial (BinaryRationalArithmetic.encode s[a])
      (BinaryRationalArithmetic.encode s[b]))) = BinaryRationalArithmetic.encode z) :
    ∃ n,
      let start := initial L (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape (s.set dst z) ∧ CleanIO (advance n start) ∧
      bitSteps n start ≤
        2*L.bitSteps nm (L.initial (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b])) +
        300*(rationalRegisterEncoding s+s.length) +
        64*(rationalEncodingLength s[a]+rationalEncodingLength s[b]) +
        128*rationalEncodingLength z+1200 := by
  obtain ⟨na, hna, hea⟩ := BinaryInterpreterCopy.load_steps s a ha
  obtain ⟨nb, hnb, heb⟩ := BinaryInterpreterCopy.load_steps s b hb
  obtain ⟨nw, hnw, hew⟩ := BinaryInterpreterCopy.store_steps s dst hd z
  let c := L.initial (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b])
  let cf := L.advance nm c
  obtain ⟨ka, hka, haRun⟩ := forward_left L
    (BinaryInterpreterRead.initial (tape s) (List.replicate a false)) na (tape s)
    (BinaryRationalArithmetic.encode s[a]) (List.replicate b false) (List.replicate dst false) hea
  obtain ⟨kb, hkb, hbRun⟩ := forward_right L
    (BinaryInterpreterRead.initial (tape s) (List.replicate b false)) nb (tape s)
    (BinaryRationalArithmetic.encode s[a]) (BinaryRationalArithmetic.encode s[b]) (List.replicate dst false) heb
  obtain ⟨km, _, hmRun, hmCost⟩ := forward_operate L c nm (tape s) (List.replicate dst false) hm
  change advance km (operatingState L c (tape s) (List.replicate dst false)) =
    storingState L cf (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (L.output cf)) at hmRun
  rw [hz] at hmRun
  obtain ⟨kw, hkw, hwRun⟩ := forward_store L cf
    (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (BinaryRationalArithmetic.encode z))
    nw (tape (s.set dst z)) (BinaryRationalArithmetic.encode z).numerator.negative hew
  let start := initial L (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
  change advance ka start = _ at haRun
  change advance kb _ = operatingState L c (tape s) (List.replicate dst false) at hbRun
  have htotal : advance (ka+(kb+(km+kw))) start =
      {storingState L cf (BinaryInterpreterWrite.haltState (BinaryRationalArithmetic.encode z).numerator.negative
        (tape (s.set dst z))) with phase := .halt} := by
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
    have hcb := bitSteps_le kb (rightState L (BinaryInterpreterRead.initial (tape s) (List.replicate b false))
      (BinaryRationalArithmetic.encode s[a]) (List.replicate dst false))
    have hcw := bitSteps_le kw (storingState L cf (BinaryInterpreterWrite.initial (tape s)
      (List.replicate dst false) (BinaryRationalArithmetic.encode z)))
    rw [tape_length] at hna hnb hnw
    change _ ≤ 2*L.bitSteps nm c + 300*(rationalRegisterEncoding s+s.length) +
      64*(rationalEncodingLength s[a]+rationalEncodingLength s[b]) +
      128*rationalEncodingLength z+1200
    omega

end IdentityTesting.BinaryInterpreterArithmetic
