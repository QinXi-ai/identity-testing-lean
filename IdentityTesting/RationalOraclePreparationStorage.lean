import IdentityTesting.RationalOraclePreparationOperands
import IdentityTesting.RationalOraclePreparationBounds
import IdentityTesting.RationalInstructionTraceStateBounds

/-! All actual initialization states have polynomial whole-tape size. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem OraclePreparationField.input_encoding {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (q : ℚ) (hq : q ∈ f.input a t σ) :
    L q ≤ allocationOracleInputLength a t σ + 3 := by
  have ht : L t ≤ allocationOracleInputLength a t σ := by unfold allocationOracleInputLength; omega
  have hσ : L σ ≤ allocationOracleInputLength a t σ := by unfold allocationOracleInputLength; omega
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  simp only [input, oraclePreparationInput, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_ofFn, List.mem_replicate] at hq
  rcases hq with ((rfl | rfl) | ⟨i, rfl⟩) | ⟨_, rfl⟩
  · omega
  · omega
  · have h := rational_entry_encoding_le a i
    unfold allocationOracleInputLength
    omega
  · omega

theorem OraclePreparationField.program_state_tape_encoding {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (s : RationalRegisters)
    (hs : s ∈ (f.program k).states (f.input a t σ)) :
    rationalRegisterEncoding s + s.length ≤
      (k + 3 + 1000000 * (k + 4) ^ 2) *
        (40000000 * oraclePreparationBase a t σ + allocationOracleInputLength a t σ + 8) := by
  have h := (f.program k).states_tape_encoding_le (f.input a t σ)
    (allocationOracleInputLength a t σ + 3) (10000000 * oraclePreparationBase a t σ)
    (f.input_encoding a t σ) (f.program_operands a t σ) s hs
  apply h.trans
  apply Nat.mul_le_mul (f.program_memory_polynomial a t σ)
  omega

end IdentityTesting.RationalComputation
