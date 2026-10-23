import IdentityTesting.BinaryRegisterWriteMachine

namespace IdentityTesting.BinaryRegisterWriteMachine
open BinaryRegisterMachine (Cell Symbol encode encode_append)

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 12 := by
  unfold transitionTrace
  split <;> (repeat' first | split | decide)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 12 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
    have h := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

def writeFuel (before : List (List Cell)) (oldWord newWord : List Cell) : ℕ :=
  (encode before).length + (1 + ((oldWord.length + 1) +
    ((newWord.length + 1) + ((newWord.length + 1) + ((encode before).length + 1)))))

theorem write_run (before after : List (List Cell)) (oldWord newWord : List Cell) :
    advance (writeFuel before oldWord newWord)
      (seekState (encode (before ++ oldWord :: after)) (List.replicate before.length false) [] newWord) =
      haltState (encode (before ++ newWord :: after)) := by
  unfold writeFuel
  rw [advance_add, encode_append, seek_prefix]
  simp only [List.append_nil]
  rw [advance_add]
  change advance ((oldWord.length + 1) +
      ((newWord.length + 1) + ((newWord.length + 1) + ((encode before).length + 1))))
      (eraseState (oldWord.map Symbol.cell ++ .boundary :: encode after) (encode before).reverse newWord) = _
  rw [advance_add, erase_word, advance_add, load_word]
  simp only [List.append_nil]
  have hn : newWord.reverse.length = newWord.length := List.length_reverse
  have hb : (encode before).reverse.length = (encode before).length := List.length_reverse
  rw [advance_add, ← hn, insert_word]
  rw [← hb, restore_run]
  simp [encode_append, encode, List.append_assoc]

theorem writeFuel_le (before after : List (List Cell)) (oldWord newWord : List Cell) :
    writeFuel before oldWord newWord ≤
      2 * (encode (before ++ oldWord :: after)).length + 2 * newWord.length + 5 := by
  simp only [writeFuel, encode_append, encode, List.length_append, List.length_map,
    List.length_cons]
  omega

/-- Replacement consumes its input tape, preserves every other record, and clears scratch. -/
theorem binary_register_write (before after : List (List Cell)) (oldWord newWord : List Cell) :
    ∃ fuel, advance fuel
      (seekState (encode (before ++ oldWord :: after)) (List.replicate before.length false) [] newWord) =
      haltState (encode (before ++ newWord :: after)) ∧
      bitSteps fuel (seekState (encode (before ++ oldWord :: after))
        (List.replicate before.length false) [] newWord) ≤
        24 * (encode (before ++ oldWord :: after)).length + 24 * newWord.length + 60 := by
  refine ⟨writeFuel before oldWord newWord, write_run before after oldWord newWord, ?_⟩
  have h := bitSteps_le (writeFuel before oldWord newWord)
    (seekState (encode (before ++ oldWord :: after)) (List.replicate before.length false) [] newWord)
  have hf := writeFuel_le before after oldWord newWord
  omega

end IdentityTesting.BinaryRegisterWriteMachine
