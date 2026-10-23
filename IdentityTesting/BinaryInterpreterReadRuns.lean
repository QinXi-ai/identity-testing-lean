import IdentityTesting.BinaryInterpreterRead

namespace IdentityTesting.BinaryInterpreterRead
open BinaryRegisterMachine (Cell Symbol encode)
open BinaryRationalRegisters RationalComputation

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 14 := by
  have hr := BinaryRegisterMachine.transitionTrace_length (reader s)
  have hs := BinaryRationalRecordMachine.transitionTrace_length (splitter s)
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 14*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have ht := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

/-- One combined machine reads the selected record and parses it into rational
Bool stacks. The shared record tape is never copied at the phase boundary. -/
theorem read_parse_run (before after : List (List Cell)) (w : BinaryRationalArithmetic.Word) :
    ∃ n, advance n (initial (encode (before ++ wordCells w :: after))
        (List.replicate before.length false)) =
        haltState (encode (before ++ wordCells w :: after)) w ∧
      bitSteps n (initial (encode (before ++ wordCells w :: after))
        (List.replicate before.length false)) ≤
        42 * (encode (before ++ wordCells w :: after)).length + 28*w.length + 126 := by
  obtain ⟨nr, hnr, hr⟩ := forward_read
    (BinaryRegisterMachine.seekState (encode (before ++ wordCells w :: after))
      (List.replicate before.length false) [])
    (BinaryRegisterMachine.readFuel before (wordCells w))
    (encode (before ++ wordCells w :: after)) (wordCells w)
    (BinaryRegisterMachine.read_run before after (wordCells w))
  obtain ⟨ns, hns, hs⟩ := forward_split
    (BinaryRationalRecordMachine.initial (wordCells w))
    (BinaryRationalRecordMachine.splitFuel w) (encode (before ++ wordCells w :: after)) w
    (BinaryRationalRecordMachine.split_run w)
  refine ⟨nr+ns, ?_, ?_⟩
  · change advance (nr+ns) (readingState
      (BinaryRegisterMachine.seekState (encode (before ++ wordCells w :: after))
        (List.replicate before.length false) [])) = _
    rw [advance_add, hr, hs]
  · have hb := bitSteps_le (nr+ns) (initial (encode (before ++ wordCells w :: after))
      (List.replicate before.length false))
    have hrf := BinaryRegisterMachine.readFuel_le before after (wordCells w)
    rw [BinaryRationalRecordMachine.splitFuel_eq] at hns
    omega

theorem binary_rational_register_load (s : RationalRegisters) (i : ℕ) (hi : i < s.length) :
    ∃ n, advance n (initial (tape s) (List.replicate i false)) =
        haltState (tape s) (BinaryRationalArithmetic.encode s[i]) ∧
      bitSteps n (initial (tape s) (List.replicate i false)) ≤
        42 * (rationalRegisterEncoding s + s.length) + 28 * rationalEncodingLength s[i] + 126 := by
  have h := read_parse_run (records (s.take i)) (records (s.drop (i+1)))
    (BinaryRationalArithmetic.encode s[i])
  simp only [show wordCells (BinaryRationalArithmetic.encode s[i]) = rationalCells s[i] from rfl] at h
  change ∃ n, advance n (initial (encode (records (s.take i) ++ rationalCells s[i] ::
    records (s.drop (i+1)))) (List.replicate (records (s.take i)).length false)) =
    haltState (encode (records (s.take i) ++ rationalCells s[i] :: records (s.drop (i+1))))
      (BinaryRationalArithmetic.encode s[i]) ∧ _ at h
  have hlen : (records (s.take i)).length = i := by simp [records, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← records_decomposition s i hi, ← tape, hlen, tape_length,
    BinaryRationalArithmetic.encode_length] at h
  exact h

end IdentityTesting.BinaryInterpreterRead
