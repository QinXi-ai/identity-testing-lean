import IdentityTesting.RationalAlgorithmTraceEvaluation
import IdentityTesting.RationalAlgorithmTraceVectorBounds

/-! Every operand of the actual reusable evaluator, including control copies. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem oracleIntervalValue_encoding {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t β ρ : ℚ) :
    L (oracleIntervalValue objective a t β ρ n).1 ≤ 400 * k * oracleTraceSize a β t ρ n + 3 ∧
      L (oracleIntervalValue objective a t β ρ n).2 ≤ 400 * k * oracleTraceSize a β t ρ n + 3 := by
  have hl := oraclePartialSum_encoding a β t ρ n objective false (List.finRange k) (by simp)
  have hu := oraclePartialSum_encoding a β t ρ n objective true (List.finRange k) (by simp)
  cases objective <;> simpa [oraclePartialSum, oracleIntervalValue, oracleTermValue,
    oracleObjectiveInterval, oracleBudgetInterval, List.finRange, List.map_ofFn, List.sum_ofFn] using And.intro hl hu

def oracleEvaluationCleanupCalls : List RationalCall :=
  [⟨.copy, 0, 0⟩, ⟨.copy, 0, 0⟩, ⟨.copy, 0, 0⟩,
   ⟨.copy, 1, 0⟩, ⟨.copy, 0, 0⟩, ⟨.copy, 0, 0⟩]

theorem oracleEvaluateProgram_trace {k : ℕ} (objective : Bool) (n betaIndex : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m β : ℚ)
    (hβ : (RationalOperand.reg betaIndex).read
      (oracleMachineState a t ρ l u ζ margin ol ou done m) = β) :
    ((oracleEvaluateProgram objective k n betaIndex).run
      (oracleMachineState a t ρ l u ζ margin ol ou done m)).2 =
      [⟨.copy, β, 0⟩] ++ ((oracleVectorProgram objective k n).run (oracleProgramInput a t β ρ)).2 ++
      [⟨.copy, (oracleIntervalValue objective a t β ρ n).1, 0⟩,
        ⟨.copy, (oracleIntervalValue objective a t β ρ n).2, 0⟩] ++ oracleEvaluationCleanupCalls := by
  obtain ⟨z, x, y, hv⟩ := oracleVectorProgram_final objective n a t β ρ
  have hp : (rationalAssign 9 .copy (.reg betaIndex) (.literal 0)).exec
      (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      [l, u, ζ, margin, ol, ou, done, m] ++ oracleProgramInput a t β ρ := by
    simp only [rationalAssign, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalCall.result, RationalOp.eval, hβ]
    simp [oracleMachineState, oracleProgramInput, oracleRegisters, coordinateRegisters]
  have hr := (oracleVectorProgram objective k n).shift_run
    [l, u, ζ, margin, ol, ou, done, m] (oracleProgramInput a t β ρ)
  have he := (oracleVectorProgram objective k n).shift_exec
    [l, u, ζ, margin, ol, ou, done, m] (oracleProgramInput a t β ρ)
  simp only [List.length_cons, List.length_nil] at hr he
  simp only [oracleEvaluateProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.run_seq_trace, RationalProgram.run_result, RationalProgram.exec, hp, he, hv]
  rw [hr]
  simp only [oracleMachineState, oracleProgramInput, oracleRegisters, coordinateRegisters,
    RationalOperand.read, List.cons_append, List.nil_append] at hβ
  simp [oracleEvaluateCleanup, rationalSequence, rationalAssign, oracleMachineState,
    oracleProgramInput, oracleRegisters, coordinateRegisters, oracleEvaluationCleanupCalls,
    RationalProgram.run, RationalProgram.exec, RationalInstruction.exec, RationalInstruction.call,
    RationalOperand.read, RationalCall.result, RationalOp.eval, hβ, List.append_assoc]

theorem oracleEvaluateProgram_operand_encoding {k : ℕ} (objective : Bool) (n betaIndex : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m β : ℚ)
    (hβ : (RationalOperand.reg betaIndex).read
      (oracleMachineState a t ρ l u ζ margin ol ou done m) = β)
    (c : RationalCall) (hc : c ∈ ((oracleEvaluateProgram objective k n betaIndex).run
      (oracleMachineState a t ρ l u ζ margin ol ou done m)).2) :
    L c.lhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n ∧
      L c.rhs ≤ 1000000 * (k + 1) * oracleTraceSize a β t ρ n := by
  rw [oracleEvaluateProgram_trace objective n betaIndex a t ρ l u ζ margin ol ou done m β hβ] at hc
  have hi := oracleIntervalValue_encoding objective n a t β ρ
  have hb : 1 ≤ oracleTraceSize a β t ρ n := by unfold oracleTraceSize; omega
  have hβb : L β ≤ oracleTraceSize a β t ρ n := by unfold oracleTraceSize; omega
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · simp only [List.mem_singleton] at hc
    subst c
    simp only [RationalCall.lhs, RationalCall.rhs]
    constructor <;> nlinarith
  · exact oracleVectorProgram_operand_encoding a β t ρ n objective c hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp only [RationalCall.lhs, RationalCall.rhs] <;>
      constructor <;> nlinarith [hi.1, hi.2]
  · simp only [oracleEvaluationCleanupCalls, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [RationalCall.lhs, RationalCall.rhs] <;> constructor <;> nlinarith

end IdentityTesting.RationalComputation
