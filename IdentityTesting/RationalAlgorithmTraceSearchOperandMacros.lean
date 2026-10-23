import IdentityTesting.RationalAlgorithmTraceSearchExec
import IdentityTesting.RationalAlgorithmTraceEvaluationOperands

/-! Operand bounds for the terminating branches of the actual search program. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem oracleNarrowProgram_trace {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) :
    ((oracleNarrowProgram k n).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2 =
      ((oracleEvaluateProgram true k n 0).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2 ++
      [⟨.copy, (oracleObjectiveInterval a l ρ n).1, 0⟩] ++
      ((oracleEvaluateProgram true k n 1).run (oracleMachineState a t ρ l u ζ margin
        (oracleObjectiveInterval a l ρ n).1 (oracleObjectiveInterval a l ρ n).2 done
        (oracleObjectiveInterval a l ρ n).1)).2 ++
      [⟨.copy, (oracleObjectiveInterval a l ρ n).1, 0⟩, ⟨.copy, 1, 0⟩] := by
  simp only [oracleNarrowProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.run_seq_trace, RationalProgram.exec, oracleEvaluateProgram_exec_0,
    oracleEvaluateProgram_exec_1, oracleIntervalValue, if_true,
    oracleMachine_save, oracleMachine_restore, oracleMachine_done]
  simp only [rationalAssign, RationalProgram.run, RationalInstruction.call, oracleMachine_read4,
    oracleMachine_read7, rationalLiteral_read, List.append_nil, List.singleton_append,
    List.append_assoc, List.cons_append, List.nil_append]

theorem oracleAmbiguousProgram_trace {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) :
    ((oracleAmbiguousProgram k n).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2 =
      ((oracleEvaluateProgram true k n 7).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2 ++
      [⟨.sub, (oracleObjectiveInterval a m ρ n).1, margin⟩,
        ⟨.add, (oracleObjectiveInterval a m ρ n).2, margin⟩, ⟨.copy, 1, 0⟩] := by
  simp only [oracleAmbiguousProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.run_seq_trace, RationalProgram.exec, oracleEvaluateProgram_exec_7,
    oracleIntervalValue, if_true, oracleMachine_subtract, oracleMachine_addMargin,
    oracleMachine_done]
  simp only [rationalAssign, RationalProgram.run, RationalInstruction.call, oracleMachine_read3,
    oracleMachine_read4, oracleMachine_read5, rationalLiteral_read,
    List.append_nil, List.singleton_append, List.append_assoc]

def oracleControlSize {k : ℕ} (a : Fin k → ℚ) (t ρ ζ margin l u : ℚ) (n : ℕ) : ℕ :=
  rationalVectorEncodingLength a + L t + L ρ + L ζ + L margin + L l + L u + n + 1

theorem oracleNarrowProgram_operand_encoding {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) (c : RationalCall)
    (hc : c ∈ ((oracleNarrowProgram k n).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2) :
    L c.lhs ≤ 1000000 * (k + 1) * oracleControlSize a t ρ ζ margin l u n ∧
      L c.rhs ≤ 1000000 * (k + 1) * oracleControlSize a t ρ ζ margin l u n := by
  have hl : oracleTraceSize a l t ρ n ≤ oracleControlSize a t ρ ζ margin l u n := by
    unfold oracleTraceSize oracleControlSize; omega
  have hu : oracleTraceSize a u t ρ n ≤ oracleControlSize a t ρ ζ margin l u n := by
    unfold oracleTraceSize oracleControlSize; omega
  have hmL := Nat.mul_le_mul_left (1000000 * (k + 1)) hl
  have hmU := Nat.mul_le_mul_left (1000000 * (k + 1)) hu
  have hJl := oracleIntervalValue_encoding true n a t l ρ
  simp only [oracleIntervalValue, if_true] at hJl
  have hscale : 1 ≤ oracleControlSize a t ρ ζ margin l u n := by unfold oracleControlSize; omega
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  rw [oracleNarrowProgram_trace] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with hc | rfl | hc | rfl | rfl
  · have h := oracleEvaluateProgram_operand_encoding true n 0 a t ρ l u ζ margin ol ou done m l rfl c hc
    exact ⟨h.1.trans hmL, h.2.trans hmL⟩
  · simp only [RationalCall.lhs, RationalCall.rhs]
    constructor <;> nlinarith [hJl.1]
  · have h := oracleEvaluateProgram_operand_encoding true n 1 a t ρ l u ζ margin
      (oracleObjectiveInterval a l ρ n).1 (oracleObjectiveInterval a l ρ n).2 done
      (oracleObjectiveInterval a l ρ n).1 u rfl c hc
    exact ⟨h.1.trans hmU, h.2.trans hmU⟩
  · simp only [RationalCall.lhs, RationalCall.rhs]
    constructor <;> nlinarith [hJl.1]
  · simp only [RationalCall.lhs, RationalCall.rhs]
    constructor <;> nlinarith

theorem oracleAmbiguousProgram_operand_encoding {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) (c : RationalCall)
    (hc : c ∈ ((oracleAmbiguousProgram k n).run (oracleMachineState a t ρ l u ζ margin ol ou done m)).2) :
    L c.lhs ≤ 1000000 * (k + 1) * (oracleTraceSize a m t ρ n + L margin) ∧
      L c.rhs ≤ 1000000 * (k + 1) * (oracleTraceSize a m t ρ n + L margin) := by
  have hj := oracleIntervalValue_encoding true n a t m ρ
  simp only [oracleIntervalValue, if_true] at hj
  have hs : 1 ≤ oracleTraceSize a m t ρ n := by unfold oracleTraceSize; omega
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  rw [oracleAmbiguousProgram_trace] at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | rfl | rfl | rfl
  · have h := oracleEvaluateProgram_operand_encoding true n 7 a t ρ l u ζ margin ol ou done m m rfl c hc
    have hm := Nat.mul_le_mul_left (1000000 * (k + 1))
      (Nat.le_add_right (oracleTraceSize a m t ρ n) (L margin))
    exact ⟨h.1.trans hm, h.2.trans hm⟩
  all_goals simp only [RationalCall.lhs, RationalCall.rhs]; constructor <;> nlinarith [hj.1, hj.2]

end IdentityTesting.RationalComputation
