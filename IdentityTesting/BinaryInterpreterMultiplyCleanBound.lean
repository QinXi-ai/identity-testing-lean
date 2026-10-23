import IdentityTesting.BinaryInterpreterMultiplyClean

namespace IdentityTesting.BinaryInterpreterMultiplyClean
open BinaryRationalRegisters RationalComputation

def initial (tape : List BinaryRegisterMachine.Symbol) (a b dst : List Bool) : State :=
  runningState (BinaryInterpreterMultiply.initial tape a b dst)

theorem binary_multiply_instruction_with_cleanup (s : RationalRegisters) (a b dst : ℕ)
    (ha : a < s.length) (hb : b < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := initial (tape s) (List.replicate a false) (List.replicate b false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).core.tape = tape ((BinaryInterpreterMultiply.multiplyInstruction a b dst).exec s) ∧
      BinaryInterpreterMultiply.CleanIO (advance n start).core ∧
      (∀ i, BinaryMultiplierStorage.tapes (advance n start).core.core i = []) ∧
      bitSteps n start ≤ 1500*(rationalRegisterEncoding s+s.length) +
        1000000*(rationalEncodingLength s[a]+rationalEncodingLength s[b]+1)^3 := by
  let r := BinaryInterpreterMultiply.initial (tape s) (List.replicate a false)
    (List.replicate b false) (List.replicate dst false)
  obtain ⟨n, hh, ht, hio, hc⟩ := BinaryInterpreterMultiply.binary_rational_register_multiply s a b dst ha hb hd
  change (BinaryInterpreterMultiply.advance n r).phase = .halt at hh
  change (BinaryInterpreterMultiply.advance n r).tape = _ at ht
  change BinaryInterpreterMultiply.CleanIO (BinaryInterpreterMultiply.advance n r) at hio
  change BinaryInterpreterMultiply.bitSteps n r ≤ _ at hc
  let final := BinaryInterpreterMultiply.advance n r
  let count := 69 + BinaryWorkspaceAdapters.rationalMultiplierCells final.core
  have hclear := BinaryMultiplierStorage.clear_all final.core
  change (BinaryMultiplierStorage.advance count (BinaryMultiplierStorage.initial final.core)).cursor.val = 0 ∧
    (∀ i, BinaryMultiplierStorage.tapes (BinaryMultiplierStorage.advance count
      (BinaryMultiplierStorage.initial final.core)).core i = []) ∧
    BinaryMultiplierStorage.bitSteps count (BinaryMultiplierStorage.initial final.core) ≤ 3*count at hclear
  obtain ⟨kr, _, hr, hrc⟩ := forward_running r n hh
  obtain ⟨kc, _, hcr, hcc⟩ := forward_cleaning final (BinaryMultiplierStorage.initial final.core) count hclear.1
  have he : advance (kr+kc) (runningState r) =
      {cleaningState final (BinaryMultiplierStorage.advance count (BinaryMultiplierStorage.initial final.core))
        with phase := .halt} := by
    rw [advance_add, hr]
    exact hcr
  refine ⟨kr+kc, ?_, ?_, ?_, ?_, ?_⟩
  · change (advance _ (runningState r)).phase = _
    rw [he]
  · change (advance _ (runningState r)).core.tape = _
    rw [he]
    change final.tape = _
    rw [BinaryInterpreterMultiply.multiplyInstruction_exec s a b dst ha hb]
    exact ht
  · change BinaryInterpreterMultiply.CleanIO (advance _ (runningState r)).core
    rw [he]
    exact hio
  · change ∀ i, BinaryMultiplierStorage.tapes (advance _ (runningState r)).core.core i = []
    rw [he]
    exact hclear.2.1
  · change bitSteps (kr+kc) (runningState r) ≤ _
    rw [bitSteps_add, hr]
    have hgrowth := BinaryInterpreterMultiply.core_advance_cost n r
    have hzero : BinaryWorkspaceAdapters.rationalMultiplierCells r.core = 0 := rfl
    rw [hzero, zero_add] at hgrowth
    change BinaryWorkspaceAdapters.rationalMultiplierCells final.core ≤
      BinaryInterpreterMultiply.bitSteps n r at hgrowth
    let S := rationalEncodingLength s[a]+rationalEncodingLength s[b]+1
    have hpos : 0 < S^3 := by dsimp [S]; positivity
    have hone : 1 ≤ S^3 := by omega
    change BinaryInterpreterMultiply.bitSteps n r ≤
      150*(rationalRegisterEncoding s+s.length)+100000*S^3 at hc
    change _ ≤ 1500*(rationalRegisterEncoding s+s.length)+1000000*S^3
    have hcCount : count = 69 + BinaryWorkspaceAdapters.rationalMultiplierCells final.core := rfl
    nlinarith only [hrc, hcc, hclear.2.2, hgrowth, hc, hone, hcCount]

end IdentityTesting.BinaryInterpreterMultiplyClean
