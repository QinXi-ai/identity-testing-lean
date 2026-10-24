import IdentityTesting.RationalExpressionSequence
import IdentityTesting.RationalOraclePreparationProgram
import IdentityTesting.RationalAlgorithmTraceAllocationSearch

/-! A dimension-dependent initializer computes the complete search register
block and its two runtime counters from the original rational inputs. -/
namespace IdentityTesting.RationalComputation

def oraclePreparedLiteral (q : ℚ) : RationalPreparedExpr := ⟨.literal q, false⟩
def oraclePreparedRegister (i : ℕ) : RationalPreparedExpr := ⟨.reg i, false⟩
def oraclePreparedField (k : ℕ) (f : OraclePreparationField) : RationalPreparedExpr :=
  ⟨f.expression k, false⟩
def oraclePreparedCount (k : ℕ) (f : OraclePreparationField) : RationalPreparedExpr :=
  ⟨f.expression k, true⟩

def oracleInitializerExpressions (k : ℕ) : List RationalPreparedExpr :=
  [oraclePreparedField (k + 1) .lower, oraclePreparedField (k + 1) .upper,
    oraclePreparedField (k + 1) .tolerance, oraclePreparedField (k + 1) .margin] ++
  List.replicate 7 (oraclePreparedLiteral 0) ++ [oraclePreparedLiteral 1] ++
  List.replicate 9 (oraclePreparedLiteral 0) ++
  [oraclePreparedRegister 0, oraclePreparedField (k + 1) .pole,
    oraclePreparedLiteral 0, oraclePreparedLiteral 0] ++
  List.ofFn (fun i : Fin (k + 1) => oraclePreparedRegister (2 + i)) ++
  [oraclePreparedCount (k + 1) .innerRatio, oraclePreparedCount (k + 1) .outerRatio]

theorem oracleInitializerExpressions_length (k : ℕ) :
    (oracleInitializerExpressions k).length = k + 28 := by
  simp [oracleInitializerExpressions]

theorem oracleInitializerExpressions_inputs (k : ℕ) (e : RationalPreparedExpr)
    (he : e ∈ oracleInitializerExpressions k) : e.expression.inputs ≤ k + 3 := by
  simp only [oracleInitializerExpressions, List.mem_append, or_assoc] at he
  rcases he with h | h | h | h | h | h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact OraclePreparationField.inputs_le .lower k
    · exact OraclePreparationField.inputs_le .upper k
    · exact OraclePreparationField.inputs_le .tolerance k
    · exact OraclePreparationField.inputs_le .margin k
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
    simp [oraclePreparedLiteral, RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
  · simp only [List.mem_singleton] at h
    subst e
    simp [oraclePreparedLiteral, RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp h
    simp [oraclePreparedLiteral, RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · simp [oraclePreparedRegister, RationalExpr.reg, RationalExpr.inputs, RationalOperand.slots]
    · exact OraclePreparationField.inputs_le .pole k
    · simp [oraclePreparedLiteral, RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
    · simp [oraclePreparedLiteral, RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    simp only [oraclePreparedRegister, RationalExpr.reg, RationalExpr.inputs, RationalOperand.slots]
    have := i.isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact OraclePreparationField.inputs_le .innerRatio k
    · exact OraclePreparationField.inputs_le .outerRatio k

theorem oracleInitializerExpressions_values {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    (oracleInitializerExpressions k).map (fun e => e.eval (oraclePreparationInput a t σ scratch)) =
      allocationOracleSearchInput a t σ ++
        [(allocationInnerPrecision a t σ : ℚ), (allocationOuterFuel a t σ : ℚ)] := by
  have field (f : OraclePreparationField) := f.expression_eval a t σ scratch
  have atom (i : Fin (k + 1)) := oraclePreparationInput_readAtom a t σ scratch i
  simp only [oracleInitializerExpressions, List.map_append, List.map_cons, List.map_nil,
    List.map_replicate, List.map_ofFn, Function.comp_apply,
    oraclePreparedField, oraclePreparedCount, oraclePreparedLiteral, oraclePreparedRegister,
    RationalPreparedExpr.eval, Bool.false_eq_true, if_false, if_true, field,
    RationalExpr.literal, RationalExpr.reg, RationalExpr.eval, oraclePreparationInput_read0, atom]
  simp only [Function.comp_def, RationalPreparedExpr.eval, if_false, Bool.false_eq_true,
    RationalExpr.eval, atom]
  simp only [RationalOperand.read]
  simp only [allocationOracleSearchInput, oracleMachineState, oracleProgramInput,
    oracleRegisters, coordinateRegisters, OraclePreparationField.value,
    allocationInnerPrecision, allocationOuterFuel, oracleDyadicPrecision]
  simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
    List.append_assoc]

end IdentityTesting.RationalComputation
