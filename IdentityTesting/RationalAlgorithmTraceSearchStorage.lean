import IdentityTesting.RationalInstructionTraceStateBounds
import IdentityTesting.RationalAlgorithmTraceAllocationOperands
import IdentityTesting.RationalAlgorithmTraceStorage

/-! Entire register-tape bounds at every executed search state. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem oracleSearchInput_encoding {k : ℕ} (a : Fin k → ℚ) (t ρ ζ margin b B : ℚ)
    (n fuel : ℕ) (q : ℚ)
    (hq : q ∈ oracleMachineState a t ρ b B ζ margin 0 0 0 0) :
    L q ≤ oracleSearchTraceSize a t ρ ζ margin b B n fuel + 3 := by
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  simp only [oracleMachineState, oracleProgramInput, oracleRegisters, coordinateRegisters,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_ofFn] at hq
  rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl)) | ⟨i, rfl⟩
  all_goals first
    | (unfold oracleSearchTraceSize; omega)
    | (have := rational_entry_encoding_le a i; unfold oracleSearchTraceSize; omega)

theorem oracleSearchProgram_state_encoding {k : ℕ} (n fuel : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin b B : ℚ) (s : RationalRegisters)
    (hs : s ∈ (oracleSearchProgram k n fuel).states
      (oracleMachineState a t ρ b B ζ margin 0 0 0 0)) (q : ℚ) (hq : q ∈ s) :
    L q ≤ 80000000 * (k + 1) * oracleSearchTraceSize a t ρ ζ margin b B n fuel + 3 := by
  let X := oracleSearchTraceSize a t ρ ζ margin b B n fuel
  have hx : 1 ≤ X := by dsimp [X, oracleSearchTraceSize]; omega
  have h := (oracleSearchProgram k n fuel).states_encoding_le
    (oracleMachineState a t ρ b B ζ margin 0 0 0 0) (X + 3)
    (20000000 * (k + 1) * X)
    (oracleSearchInput_encoding a t ρ ζ margin b B n fuel)
    (oracleSearchProgram_operand_encoding n fuel a t ρ ζ margin b B) s hs q hq
  change L q ≤ 80000000 * (k + 1) * X + 3
  have hmax : max (X + 3) (4 * (20000000 * (k + 1) * X) + 3) ≤
      80000000 * (k + 1) * X + 3 := by
    apply max_le <;> nlinarith
  exact h.trans hmax

theorem oracleSearchProgram_state_tape_encoding {k : ℕ} (n fuel : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin b B : ℚ) (s : RationalRegisters)
    (hs : s ∈ (oracleSearchProgram k n fuel).states
      (oracleMachineState a t ρ b B ζ margin 0 0 0 0)) :
    rationalRegisterEncoding s + s.length ≤
      (25 + k) * (80000000 * (k + 1) * oracleSearchTraceSize a t ρ ζ margin b B n fuel + 5) := by
  have h := rationalRegisterEncoding_le s _
    (oracleSearchProgram_state_encoding n fuel a t ρ ζ margin b B s hs)
  have hl := (oracleSearchProgram k n fuel).states_length
    (oracleMachineState a t ρ b B ζ margin 0 0 0 0) s hs
  rw [oracleMachineState_length] at hl
  simpa only [hl, Nat.add_assoc] using h

theorem allocationOracleSearchProgram_state_tape_encoding {k : ℕ}
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (s : RationalRegisters)
    (hs : s ∈ (oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
      (allocationOuterFuel a t σ)).states (allocationOracleSearchInput a t σ)) :
    let S := allocationOracleInputLength a t σ
    rationalRegisterEncoding s + s.length ≤
      (25 + S) * (80000000 * (S + 1) * (500 * S + 2500) + 5) := by
  dsimp only
  have h := oracleSearchProgram_state_tape_encoding (allocationInnerPrecision a t σ)
    (allocationOuterFuel a t σ) a t
    (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t))
    (σ / (100 * ∑ i, a i)) (σ / 100) (oracleBetaLower a t) (oracleBetaUpper (a 0) t) s hs
  have hsize := allocationOracleSearchTraceSize_le a t σ
  have hk : k + 1 ≤ allocationOracleInputLength a t σ := by
    unfold allocationOracleInputLength rationalVectorEncodingLength; omega
  apply h.trans
  apply Nat.mul_le_mul (Nat.add_le_add_left hk 25)
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left 80000000 (Nat.add_le_add_right hk 1)) hsize

end IdentityTesting.RationalComputation
