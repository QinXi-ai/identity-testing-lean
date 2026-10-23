import IdentityTesting.RationalAlgorithmTraceBudgetScalar
import IdentityTesting.RationalOracleEvaluationEncoding

/-! Every intermediate operand in the explicit scalar accumulation programs. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def costAccumulatorCalls (a x t s : ℚ) : List RationalCall :=
  [⟨.copy, x, 0⟩, ⟨.mul, x, x⟩, ⟨.mul, x ^ 2, x ^ 2⟩,
   ⟨.mul, t, t⟩, ⟨.mul, a, a⟩, ⟨.mul, t ^ 2, a ^ 2⟩,
   ⟨.mul, t ^ 2 * a ^ 2, x ^ 4⟩, ⟨.sub, 1, x ^ 4⟩,
   ⟨.div, t ^ 2 * a ^ 2 * x ^ 4, 1 - x ^ 4⟩,
   ⟨.add, s, rationalAllocationCost t a x⟩] ++ List.replicate 9 ⟨.copy, 0, 0⟩

theorem budgetAccumulatorProgram_trace (upper : Bool) (a β l u t ρ sl su : ℚ) :
    ((budgetAccumulatorProgram upper).run (oracleRegisters a β l u t ρ sl su)).2 =
      costAccumulatorCalls a (if upper then u else l) t (if upper then su else sl) := by
  cases upper <;>
    simp [budgetAccumulatorProgram, allocationCostProgram, coordinateClearProgram,
      rationalSequence, rationalAssign, oracleRegisters, coordinateRegisters,
      RationalProgram.run, RationalInstruction.exec, RationalInstruction.call,
      RationalOperand.read, RationalCall.result, RationalOp.eval,
      costAccumulatorCalls, rationalAllocationCost, pow_succ, mul_assoc]

theorem costAccumulatorCalls_encoding (a x t s : ℚ) (c : RationalCall)
    (hc : c ∈ costAccumulatorCalls a x t s) :
    L c.lhs ≤ 100 * (L a + L x + L t + L s + 1) ∧
      L c.rhs ≤ 100 * (L a + L x + L t + L s + 1) := by
  have hzero : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have hone : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have hx2 := rational_pow_encoding x 2
  have hx4 := rational_pow_encoding x 4
  have ht2 := rational_pow_encoding t 2
  have ha2 := rational_pow_encoding a 2
  have hta := rational_mul_encoding (t ^ 2) (a ^ 2)
  have htax := rational_mul_encoding (t ^ 2 * a ^ 2) (x ^ 4)
  have hd := rational_sub_encoding 1 (x ^ 4)
  have hcst := rationalAllocationCost_encoding_le t a x
  simp only [costAccumulatorCalls, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_replicate] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨_, rfl⟩ <;>
    simp only [RationalCall.lhs, RationalCall.rhs] <;> omega

theorem budgetAccumulatorProgram_operand_encoding (upper : Bool) (a β l u t ρ sl su : ℚ)
    (c : RationalCall) (hc : c ∈ ((budgetAccumulatorProgram upper).run
      (oracleRegisters a β l u t ρ sl su)).2) :
    L c.lhs ≤ 100 * (L a + L l + L u + L t + L sl + L su + 1) ∧
      L c.rhs ≤ 100 * (L a + L l + L u + L t + L sl + L su + 1) := by
  rw [budgetAccumulatorProgram_trace] at hc
  have h := costAccumulatorCalls_encoding a (if upper then u else l) t
    (if upper then su else sl) c hc
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at h <;>
    constructor <;> omega

theorem objectiveAccumulatorProgram_trace (upper : Bool) (a β l u t ρ sl su : ℚ) :
    ((objectiveAccumulatorProgram upper).run (oracleRegisters a β l u t ρ sl su)).2 =
      [⟨.mul, a, if upper then u else l⟩,
       ⟨.add, if upper then su else sl, a * (if upper then u else l)⟩,
       ⟨.copy, 0, 0⟩] := by
  cases upper <;>
    simp [objectiveAccumulatorProgram, rationalSequence, rationalAssign, oracleRegisters,
      coordinateRegisters, RationalProgram.run, RationalInstruction.exec,
      RationalInstruction.call, RationalOperand.read, RationalCall.result, RationalOp.eval]

theorem objectiveAccumulatorProgram_operand_encoding (upper : Bool) (a β l u t ρ sl su : ℚ)
    (c : RationalCall) (hc : c ∈ ((objectiveAccumulatorProgram upper).run
      (oracleRegisters a β l u t ρ sl su)).2) :
    L c.lhs ≤ 100 * (L a + L l + L u + L t + L sl + L su + 1) ∧
      L c.rhs ≤ 100 * (L a + L l + L u + L t + L sl + L su + 1) := by
  rw [objectiveAccumulatorProgram_trace] at hc
  have hl := rational_mul_encoding a l
  have hu := rational_mul_encoding a u
  have hzero : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true,
    List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl <;>
    simp only [RationalCall.lhs, RationalCall.rhs] <;> omega

end IdentityTesting.RationalComputation
