import IdentityTesting.BinaryRegisterMachine

namespace IdentityTesting.BinaryRegisterMachine

theorem transitionTrace_length (s : State) : (transitionTrace s).length ≤ 13 := by
  unfold transitionTrace
  split <;> (repeat' first | split | decide)

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 13 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
    have h := transitionTrace_length s
    have hi := ih (step s)
    simp only [bitSteps, Nat.mul_succ]
    omega

def readFuel (before : List (List Cell)) (word : List Cell) : ℕ :=
  (encode before).length + 1 + (word.length + 1) +
    ((word.map Symbol.cell).reverse ++ (encode before).reverse).length + 1 + (word.length + 1)

theorem read_run (before after : List (List Cell)) (word : List Cell) :
    advance (readFuel before word)
      (seekState (encode (before ++ word :: after)) (List.replicate before.length false) []) =
      haltState (encode (before ++ word :: after)) word := by
  unfold readFuel
  rw [show (encode before).length + 1 + (word.length + 1) +
      ((word.map Symbol.cell).reverse ++ (encode before).reverse).length + 1 + (word.length + 1) =
      (encode before).length + (1 + ((word.length + 1) +
      ((((word.map Symbol.cell).reverse ++ (encode before).reverse).length + 1) + (word.length + 1)))) by omega]
  rw [advance_add, encode_append, seek_prefix]
  simp only [List.append_nil]
  rw [advance_add]
  change advance ((word.length + 1) +
      ((((word.map Symbol.cell).reverse ++ (encode before).reverse).length + 1) + (word.length + 1)))
      (copyState (word.map Symbol.cell ++ .boundary :: encode after) (encode before).reverse [] []) = _
  rw [advance_add, copy_word]
  simp only [List.append_nil]
  rw [advance_add, restore_run]
  have hrev : (word.reverse).length = word.length := List.length_reverse
  rw [← hrev, output_run]
  simp [encode_append, encode, List.reverse_append, List.reverse_reverse, List.append_assoc]

theorem readFuel_le (before after : List (List Cell)) (word : List Cell) :
    readFuel before word ≤ 3 * (encode (before ++ word :: after)).length + 4 := by
  simp only [readFuel, encode_append, encode, List.length_append, List.length_map,
    List.length_reverse, List.length_cons]
  omega

/-- An actual sequential read restores the source and empties all scratch tapes. -/
theorem binary_register_read (before after : List (List Cell)) (word : List Cell) :
    ∃ fuel, advance fuel
      (seekState (encode (before ++ word :: after)) (List.replicate before.length false) []) =
      haltState (encode (before ++ word :: after)) word ∧
      bitSteps fuel (seekState (encode (before ++ word :: after))
        (List.replicate before.length false) []) ≤
        39 * (encode (before ++ word :: after)).length + 52 := by
  refine ⟨readFuel before word, read_run before after word, ?_⟩
  have h := bitSteps_le (readFuel before word)
    (seekState (encode (before ++ word :: after)) (List.replicate before.length false) [])
  have hf := readFuel_le before after word
  omega

end IdentityTesting.BinaryRegisterMachine
