import IdentityTesting.BinaryInterpreterCopy

namespace IdentityTesting.BinaryInterpreterCopy
open BinaryRationalRegisters RationalComputation

theorem load_steps (s : RationalRegisters) (src : ℕ) (hs : src < s.length) :
    ∃ n, n ≤ 3*(tape s).length + 2*rationalEncodingLength s[src] + 9 ∧
      BinaryInterpreterRead.advance n (BinaryInterpreterRead.initial (tape s) (List.replicate src false)) =
        BinaryInterpreterRead.haltState (tape s) (BinaryRationalArithmetic.encode s[src]) := by
  have h := BinaryInterpreterRead.read_parse_steps (records (s.take src))
    (records (s.drop (src+1))) (BinaryRationalArithmetic.encode s[src])
  simp only [show wordCells (BinaryRationalArithmetic.encode s[src]) = rationalCells s[src] from rfl] at h
  have hlen : (records (s.take src)).length = src := by simp [records, Nat.min_eq_left (Nat.le_of_lt hs)]
  rw [← records_decomposition s src hs, ← tape, hlen, BinaryRationalArithmetic.encode_length] at h
  exact h

theorem store_steps (s : RationalRegisters) (dst : ℕ) (hd : dst < s.length) (q : ℚ) :
    ∃ n, n ≤ 2*(tape s).length + 4*rationalEncodingLength q + 13 ∧
      BinaryInterpreterWrite.advance n (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false)
        (BinaryRationalArithmetic.encode q)) =
        BinaryInterpreterWrite.haltState (BinaryRationalArithmetic.encode q).numerator.negative (tape (s.set dst q)) := by
  have h := BinaryInterpreterWrite.join_write_steps (records (s.take dst))
    (records (s.drop (dst+1))) (rationalCells s[dst]) (BinaryRationalArithmetic.encode q)
  simp only [show wordCells (BinaryRationalArithmetic.encode q) = rationalCells q from rfl] at h
  have hlen : (records (s.take dst)).length = dst := by simp [records, Nat.min_eq_left (Nat.le_of_lt hd)]
  rw [← records_decomposition s dst hd, ← records_set s dst hd q, ← tape, ← tape,
    hlen, BinaryRationalArithmetic.encode_length] at h
  exact h

/-- A complete finite-control copy instruction, including actual register
scanning, rational parsing, record joining, and register replacement. -/
theorem binary_rational_register_copy (s : RationalRegisters) (src dst : ℕ)
    (hs : src < s.length) (hd : dst < s.length) :
    ∃ n, advance n (initial (tape s) (List.replicate src false) (List.replicate dst false)) =
        haltState (BinaryRationalArithmetic.encode s[src]).numerator.negative (tape (s.set dst s[src])) ∧
      bitSteps n (initial (tape s) (List.replicate src false) (List.replicate dst false)) ≤
        75*(rationalRegisterEncoding s+s.length) + 90*rationalEncodingLength s[src] + 360 := by
  obtain ⟨nl, hnl, hl⟩ := load_steps s src hs
  obtain ⟨ns, hns, hst⟩ := store_steps s dst hd s[src]
  obtain ⟨kl, hkl, hle⟩ := forward_load
    (BinaryInterpreterRead.initial (tape s) (List.replicate src false)) nl (tape s)
    (BinaryRationalArithmetic.encode s[src]) (List.replicate dst false) hl
  obtain ⟨ks, hks, hse⟩ := forward_store
    (BinaryInterpreterWrite.initial (tape s) (List.replicate dst false) (BinaryRationalArithmetic.encode s[src]))
    ns (tape (s.set dst s[src])) (BinaryRationalArithmetic.encode s[src]).numerator.negative hst
  refine ⟨kl+ks, ?_, ?_⟩
  · change advance (kl+ks) (loadingState
      (BinaryInterpreterRead.initial (tape s) (List.replicate src false)) (List.replicate dst false)) = _
    rw [advance_add, hle, hse]
  · have hb := bitSteps_le (kl+ks) (initial (tape s) (List.replicate src false) (List.replicate dst false))
    rw [tape_length] at hnl hns
    omega

def copyInstruction (src dst : ℕ) : RationalInstruction :=
  ⟨dst, .copy, .reg src, .literal 0⟩

theorem copyInstruction_exec (s : RationalRegisters) (src dst : ℕ) (hs : src < s.length) :
    (copyInstruction src dst).exec s = s.set dst s[src] := by
  simp [copyInstruction, RationalInstruction.exec, RationalInstruction.call,
    RationalCall.result, RationalOp.eval, RationalOperand.read, List.getElem?_eq_getElem hs]

theorem binary_copy_instruction (s : RationalRegisters) (src dst : ℕ)
    (hs : src < s.length) (hd : dst < s.length) :
    ∃ n, advance n (initial (tape s) (List.replicate src false) (List.replicate dst false)) =
        haltState (BinaryRationalArithmetic.encode s[src]).numerator.negative
          (tape ((copyInstruction src dst).exec s)) ∧
      bitSteps n (initial (tape s) (List.replicate src false) (List.replicate dst false)) ≤
        75*(rationalRegisterEncoding s+s.length) + 90*rationalEncodingLength s[src] + 360 := by
  rw [copyInstruction_exec s src dst hs]
  exact binary_rational_register_copy s src dst hs hd

end IdentityTesting.BinaryInterpreterCopy
