import IdentityTesting.BinaryInterpreterReadRuns
import IdentityTesting.BinaryInterpreterWriteRuns

namespace IdentityTesting.BinaryInterpreterRead
open BinaryRegisterMachine (Cell encode)
open BinaryRationalRegisters

theorem read_parse_steps (before after : List (List Cell)) (w : BinaryRationalArithmetic.Word) :
    ∃ n, n ≤ 3 * (encode (before ++ wordCells w :: after)).length + 2*w.length + 9 ∧
      advance n (initial (encode (before ++ wordCells w :: after))
        (List.replicate before.length false)) = haltState (encode (before ++ wordCells w :: after)) w := by
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
  · have hrf := BinaryRegisterMachine.readFuel_le before after (wordCells w)
    rw [BinaryRationalRecordMachine.splitFuel_eq] at hns
    omega
  · change advance (nr+ns) (readingState
      (BinaryRegisterMachine.seekState (encode (before ++ wordCells w :: after))
        (List.replicate before.length false) [])) = _
    rw [advance_add, hr, hs]

end IdentityTesting.BinaryInterpreterRead

namespace IdentityTesting.BinaryInterpreterWrite
open BinaryRegisterMachine (Cell encode)
open BinaryRationalRegisters

theorem join_write_steps (before after : List (List Cell)) (oldWord : List Cell)
    (w : BinaryRationalArithmetic.Word) :
    ∃ n, n ≤ 2 * (encode (before ++ oldWord :: after)).length + 4*w.length + 13 ∧
      advance n (initial (encode (before ++ oldWord :: after)) (List.replicate before.length false) w) =
        haltState w.numerator.negative (encode (before ++ wordCells w :: after)) := by
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
  · have hwf := BinaryRegisterWriteMachine.writeFuel_le before after oldWord (wordCells w)
    have hjf : BinaryRationalRecordJoin.joinFuel w = 2*w.length+4 := by
      simp [BinaryRationalRecordJoin.joinFuel, BinaryRationalArithmetic.Word.length]
      omega
    rw [hjf] at hnj
    rw [wordCells_length] at hwf
    omega
  · change advance (nj+nw) (joiningState (encode (before ++ oldWord :: after))
      (List.replicate before.length false) (BinaryRationalRecordJoin.initial w)) = _
    rw [advance_add, hj, hw]

end IdentityTesting.BinaryInterpreterWrite
