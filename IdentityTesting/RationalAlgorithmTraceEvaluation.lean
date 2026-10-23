import IdentityTesting.RationalAlgorithmTraceVectorResult
import IdentityTesting.RationalInstructionTraceRelocation

/-! A reusable oracle evaluator with eight persistent search registers. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators

def oracleIntervalValue {k : ℕ} (objective : Bool) (a : Fin k → ℚ)
    (t β ρ : ℚ) (n : ℕ) : ℚ × ℚ :=
  if objective then oracleObjectiveInterval a β ρ n else oracleBudgetInterval a t β ρ n

theorem oracleVectorProgram_final {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t β ρ : ℚ) :
    ∃ z l u, (oracleVectorProgram objective k n).exec (oracleProgramInput a t β ρ) =
      oracleRegisters z β l u t ρ (oracleIntervalValue objective a t β ρ n).1
        (oracleIntervalValue objective a t β ρ n).2 ++ List.ofFn a := by
  obtain ⟨z, l, u, h⟩ := oracleListProgram_exec objective n a (List.finRange k) 0 β 0 1 t ρ 0 0
  refine ⟨z, l, u, ?_⟩
  cases objective <;> simpa [oracleVectorProgram, oracleProgramInput, oracleIntervalValue,
    oracleTermValue, oracleBudgetInterval, oracleObjectiveInterval,
    List.finRange, List.map_ofFn, List.sum_ofFn] using h

def oracleMachineState {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    RationalRegisters :=
  [l, u, ζ, margin, ol, ou, done, m] ++ oracleProgramInput a t 0 ρ

def oracleEvaluateCleanup : RationalProgram := rationalSequence [
  rationalAssign 8 .copy (.literal 0) (.literal 0),
  rationalAssign 9 .copy (.literal 0) (.literal 0),
  rationalAssign 10 .copy (.literal 0) (.literal 0),
  rationalAssign 11 .copy (.literal 1) (.literal 0),
  rationalAssign 23 .copy (.literal 0) (.literal 0),
  rationalAssign 24 .copy (.literal 0) (.literal 0)]

def oracleEvaluateProgram (objective : Bool) (k n betaIndex : ℕ) : RationalProgram :=
  rationalSequence [rationalAssign 9 .copy (.reg betaIndex) (.literal 0),
    (oracleVectorProgram objective k n).shift 8,
    rationalAssign 4 .copy (.reg 23) (.literal 0),
    rationalAssign 5 .copy (.reg 24) (.literal 0), oracleEvaluateCleanup]

theorem oracleEvaluateProgram_exec {k : ℕ} (objective : Bool) (n betaIndex : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m β : ℚ)
    (hβ : (RationalOperand.reg betaIndex).read
      (oracleMachineState a t ρ l u ζ margin ol ou done m) = β) :
    (oracleEvaluateProgram objective k n betaIndex).exec
      (oracleMachineState a t ρ l u ζ margin ol ou done m) =
    oracleMachineState a t ρ l u ζ margin
      (oracleIntervalValue objective a t β ρ n).1
      (oracleIntervalValue objective a t β ρ n).2 done m := by
  obtain ⟨z, x, y, hv⟩ := oracleVectorProgram_final objective n a t β ρ
  have hp : (rationalAssign 9 .copy (.reg betaIndex) (.literal 0)).exec
      (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      [l, u, ζ, margin, ol, ou, done, m] ++ oracleProgramInput a t β ρ := by
    simp only [rationalAssign, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalCall.result, RationalOp.eval, hβ]
    simp [oracleMachineState, oracleProgramInput, oracleRegisters, coordinateRegisters]
  have hshift := (oracleVectorProgram objective k n).shift_exec
    [l, u, ζ, margin, ol, ou, done, m] (oracleProgramInput a t β ρ)
  simp only [List.length_cons, List.length_nil] at hshift
  simp only [oracleEvaluateProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.exec, hp, hshift, hv]
  simp [oracleEvaluateCleanup, rationalSequence, rationalAssign, oracleMachineState,
    oracleProgramInput, oracleRegisters, coordinateRegisters,
    RationalProgram.exec, RationalInstruction.exec, RationalInstruction.call,
    RationalOperand.read, RationalCall.result, RationalOp.eval]

theorem oracleEvaluateProgram_callBound (objective : Bool) (k n betaIndex : ℕ) :
    (oracleEvaluateProgram objective k n betaIndex).callBound ≤ k * (21 * n + 45) + 9 := by
  have hv := oracleVectorProgram_calls objective k n []
  have h : (oracleVectorProgram objective k n).callBound ≤ k * (21 * n + 45) := by
    rw [oracleVectorProgram, rationalSequence_callBound, List.map_map]
    simp only [Function.comp_def, oracleAtomProgram_callBound]
    cases objective <;> simp <;> nlinarith
  simp only [oracleEvaluateProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.callBound, RationalProgram.shift_callBound]
  have hc : oracleEvaluateCleanup.callBound = 6 := rfl
  rw [hc]
  change 1 + (_ + (1 + (1 + (6 + 0)))) ≤ _
  omega

end IdentityTesting.RationalComputation
