import IdentityTesting.BinaryInterpreterOperandExecute

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout BinaryRationalRegisters RationalComputation

/-- Enter the existing shared machine after its physical input stacks have
already been loaded. The destination may alias either source register. -/
theorem operate_store (L : Layout) (s : RationalRegisters) (dst : ℕ)
    (hd : dst < s.length) (c : L.Core) (nm : ℕ) (z : ℚ)
    (hm : L.halted (L.advance nm c) = true)
    (hz : L.output (L.advance nm c) = BinaryRationalArithmetic.encode z) :
    ∃ n,
      let start := operatingState L c (tape s) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape (s.set dst z) ∧ CleanIO (advance n start) ∧
      bitSteps n start ≤ 2*L.bitSteps nm c + 64*(rationalRegisterEncoding s+s.length) +
        128*rationalEncodingLength z+451 := by
  obtain ⟨nw, hnw, hew⟩ := BinaryInterpreterCopy.store_steps s dst hd z
  obtain ⟨km, _, hmRun, hmCost⟩ := forward_operate L c nm (tape s) (List.replicate dst false) hm
  rw [hz] at hmRun
  obtain ⟨kw, hkw, hwRun⟩ := forward_store L (L.advance nm c)
    (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (BinaryRationalArithmetic.encode z))
    nw (tape (s.set dst z)) (BinaryRationalArithmetic.encode z).numerator.negative hew
  let start := operatingState L c (tape s) (List.replicate dst false)
  have htotal : advance (km+kw) start =
      {storingState L (L.advance nm c) (BinaryInterpreterWrite.haltState
        (BinaryRationalArithmetic.encode z).numerator.negative (tape (s.set dst z))) with phase := .halt} := by
    rw [advance_add, hmRun, hwRun]
  refine ⟨km+kw, ?_, ?_, ?_, ?_⟩
  · change (advance _ start).phase = _
    rw [htotal]
  · change (advance _ start).tape = _
    rw [htotal]
    rfl
  · change CleanIO (advance _ start)
    rw [htotal]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change bitSteps (km+kw) start ≤ _
    rw [bitSteps_add, hmRun]
    have hw := bitSteps_le kw (storingState L (L.advance nm c)
      (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (BinaryRationalArithmetic.encode z)))
    rw [tape_length] at hnw
    dsimp only [start]
    omega

end IdentityTesting.BinaryInterpreterArithmetic

namespace IdentityTesting.BinaryInterpreterArithmeticClean
open BinaryInterpreterLayout BinaryInterpreterStorage BinaryRationalRegisters RationalComputation
variable {L : Layout} (W : Storage L)

theorem operate_store_clean (s : RationalRegisters) (dst : ℕ) (hd : dst < s.length)
    (c : L.Core) (nm : ℕ) (z : ℚ)
    (hm : L.halted (L.advance nm c) = true)
    (hz : L.output (L.advance nm c) = BinaryRationalArithmetic.encode z) :
    ∃ n,
      let start := runningState W (BinaryInterpreterArithmetic.operatingState L c (tape s) (List.replicate dst false))
      (advance W n start).phase = .halt ∧
      (advance W n start).core.tape = tape (s.set dst z) ∧
      BinaryInterpreterArithmetic.CleanIO (advance W n start).core ∧
      (∀ i, W.tapes (advance W n start).core.core i = []) ∧
      bitSteps W n start ≤ 16*L.bitSteps nm c + 512*(rationalRegisterEncoding s+s.length) +
        1024*rationalEncodingLength z+3610+6*(W.count+W.cells c) := by
  obtain ⟨n, hh, ht, hi, hc⟩ := BinaryInterpreterArithmetic.operate_store L s dst hd c nm z hm hz
  obtain ⟨k, hk, hkt, hki, hclear, hcost⟩ := cleanup_run W
    (BinaryInterpreterArithmetic.operatingState L c (tape s) (List.replicate dst false)) n hh
  refine ⟨k, hk, hkt.trans ht, hki hi, hclear, ?_⟩
  dsimp only [BinaryInterpreterArithmetic.operatingState] at hcost hc ⊢
  omega

end IdentityTesting.BinaryInterpreterArithmeticClean
