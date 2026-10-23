import IdentityTesting.RationalAlgorithmTraceEvaluation

/-! Every referenced register of the relocated evaluator is allocated. -/
namespace IdentityTesting.RationalComputation

theorem RationalOperand.shift_slots_le (o : RationalOperand) (d : ℕ) :
    (o.shift d).slots ≤ d + o.slots := by
  cases o <;> simp [shift, slots] <;> omega

theorem RationalProgram.shift_slots_le (p : RationalProgram) (d : ℕ) :
    (p.shift d).slots ≤ d + p.slots := by
  induction p with
  | skip => exact Nat.zero_le d
  | instr i =>
    have hl := i.lhs.shift_slots_le d
    have hr := i.rhs.shift_slots_le d
    simp only [shift, slots, RationalInstruction.shift]
    omega
  | seq p q hp hq => simp only [shift, slots]; omega
  | branchLe a b p q hp hq =>
    have ha := a.shift_slots_le d
    have hb := b.shift_slots_le d
    simp only [shift, slots]
    omega
  | «repeat» n p hp => exact hp

theorem oracleMachineState_length {k : ℕ} (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleMachineState a t ρ l u ζ margin ol ou done m).length = 25 + k := by
  simp only [oracleMachineState, List.length_append, List.length_cons, List.length_nil,
    oracleProgramInput_length]
  omega

theorem oracleEvaluateProgram_slots (objective : Bool) (k n betaIndex : ℕ)
    (hb : betaIndex < 8) : (oracleEvaluateProgram objective k n betaIndex).slots ≤ 25 + k := by
  have hv := (oracleVectorProgram objective k n).shift_slots_le 8
  have hw := oracleVectorProgram_slots objective k n
  have hc : oracleEvaluateCleanup.slots = 25 := rfl
  simp only [oracleEvaluateProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    rationalAssign, RationalProgram.slots, RationalOperand.slots]
  rw [hc]
  omega

end IdentityTesting.RationalComputation
