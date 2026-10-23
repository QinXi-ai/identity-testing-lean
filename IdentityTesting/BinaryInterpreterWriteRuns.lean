import IdentityTesting.BinaryInterpreterWrite

namespace IdentityTesting.BinaryInterpreterWrite
open BinaryRegisterMachine (Cell Symbol encode)
open BinaryRationalRegisters RationalComputation

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 13 := by
  have hj := BinaryRationalRecordJoin.transitionTrace_length (joiner s)
  have hw := BinaryRegisterWriteMachine.transitionTrace_length (writer s)
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 13*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

theorem join_write_run (before after : List (List Cell)) (oldWord : List Cell)
    (w : BinaryRationalArithmetic.Word) :
    ∃ n, advance n (initial (encode (before ++ oldWord :: after))
        (List.replicate before.length false) w) =
        haltState w.numerator.negative (encode (before ++ wordCells w :: after)) ∧
      bitSteps n (initial (encode (before ++ oldWord :: after))
        (List.replicate before.length false) w) ≤
        26 * (encode (before ++ oldWord :: after)).length + 52*w.length + 169 := by
  obtain ⟨nj, hnj, hj⟩ := forward_join (BinaryRationalRecordJoin.initial w)
    (BinaryRationalRecordJoin.joinFuel w) (encode (before ++ oldWord :: after))
    (List.replicate before.length false) w.numerator.negative (wordCells w)
    (BinaryRationalRecordJoin.join_run w)
  obtain ⟨nw, hnw, hw⟩ := forward_write
    (BinaryRegisterWriteMachine.seekState (encode (before ++ oldWord :: after))
      (List.replicate before.length false) [] (wordCells w))
    (BinaryRegisterWriteMachine.writeFuel before oldWord (wordCells w))
    (encode (before ++ wordCells w :: after)) w.numerator.negative
    (BinaryRegisterWriteMachine.write_run before after oldWord (wordCells w))
  refine ⟨nj+nw, ?_, ?_⟩
  · change advance (nj+nw) (joiningState (encode (before ++ oldWord :: after))
      (List.replicate before.length false) (BinaryRationalRecordJoin.initial w)) = _
    rw [advance_add, hj, hw]
  · have hb := bitSteps_le (nj+nw) (initial (encode (before ++ oldWord :: after))
      (List.replicate before.length false) w)
    have hwf := BinaryRegisterWriteMachine.writeFuel_le before after oldWord (wordCells w)
    have hjf : BinaryRationalRecordJoin.joinFuel w = 2*w.length+4 := by
      simp [BinaryRationalRecordJoin.joinFuel, BinaryRationalArithmetic.Word.length]
      omega
    rw [hjf] at hnj
    rw [wordCells_length] at hwf
    omega

theorem binary_rational_register_store (s : RationalRegisters) (i : ℕ) (hi : i < s.length) (q : ℚ) :
    ∃ n, advance n (initial (tape s) (List.replicate i false) (BinaryRationalArithmetic.encode q)) =
        haltState (BinaryRationalArithmetic.encode q).numerator.negative (tape (s.set i q)) ∧
      bitSteps n (initial (tape s) (List.replicate i false) (BinaryRationalArithmetic.encode q)) ≤
        26 * (rationalRegisterEncoding s + s.length) + 52 * rationalEncodingLength q + 169 := by
  have h := join_write_run (records (s.take i)) (records (s.drop (i+1)))
    (rationalCells s[i]) (BinaryRationalArithmetic.encode q)
  change ∃ n, advance n (initial (encode (records (s.take i) ++ rationalCells s[i] ::
    records (s.drop (i+1)))) (List.replicate (records (s.take i)).length false) (BinaryRationalArithmetic.encode q)) =
    haltState (BinaryRationalArithmetic.encode q).numerator.negative
      (encode (records (s.take i) ++ rationalCells q :: records (s.drop (i+1)))) ∧ _ at h
  have hlen : (records (s.take i)).length = i := by simp [records, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← records_decomposition s i hi, ← records_set s i hi q, ← tape, ← tape,
    hlen, tape_length, BinaryRationalArithmetic.encode_length] at h
  exact h

end IdentityTesting.BinaryInterpreterWrite
