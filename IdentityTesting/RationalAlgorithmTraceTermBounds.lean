import IdentityTesting.RationalAlgorithmTraceOracle
import IdentityTesting.RationalAlgorithmTraceScalarBounds
import IdentityTesting.RationalAlgorithmTraceCoordinateBounds

/-! Bounds on all executed operands in one oracle term. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

theorem RationalProgram.run_seq_trace (p q : RationalProgram) (s : RationalRegisters) :
    ((.seq p q : RationalProgram).run s).2 =
      (p.run s).2 ++ (q.run (p.exec s)).2 := by
  simp only [RationalProgram.run, RationalProgram.run_result]

def coordinateClipCalls (u ρ : ℚ) : List RationalCall :=
  [⟨.sub, 1, ρ⟩, ⟨.le, u, 1 - ρ⟩] ++
    (if u ≤ 1 - ρ then [] else [⟨.copy, 1 - ρ, 0⟩]) ++ [⟨.copy, 0, 0⟩]

theorem coordinateClipProgram_trace (a β l u t ρ sl su : ℚ) :
    (coordinateClipProgram.run (oracleRegisters a β l u t ρ sl su)).2 =
      coordinateClipCalls u ρ := by
  simp [coordinateClipProgram, coordinateClipCalls, rationalSequence, rationalAssign,
    oracleRegisters, coordinateRegisters, RationalProgram.run, RationalInstruction.exec,
    RationalInstruction.call, RationalOperand.read, RationalCall.result, RationalOp.eval]
  split <;> simp_all

theorem coordinateClipCalls_encoding (u ρ : ℚ) (c : RationalCall)
    (hc : c ∈ coordinateClipCalls u ρ) :
    L c.lhs ≤ L u + 2 * L ρ + 10 ∧ L c.rhs ≤ L u + 2 * L ρ + 10 := by
  have hd := rational_sub_encoding 1 ρ
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  by_cases h : u ≤ 1 - ρ
  · simp only [coordinateClipCalls, if_pos h, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [RationalCall.lhs, RationalCall.rhs] <;> omega
  · simp only [coordinateClipCalls, if_neg h, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp only [RationalCall.lhs, RationalCall.rhs] <;> omega

def accumulatorCalls (objective : Bool) (a x t s : ℚ) : List RationalCall :=
  if objective then [⟨.mul, a, x⟩, ⟨.add, s, a * x⟩, ⟨.copy, 0, 0⟩]
  else costAccumulatorCalls a x t s

theorem accumulatorCalls_encoding (objective : Bool) (a x t s : ℚ) (c : RationalCall)
    (hc : c ∈ accumulatorCalls objective a x t s) :
    L c.lhs ≤ 100 * (L a + L x + L t + L s + 1) ∧
      L c.rhs ≤ 100 * (L a + L x + L t + L s + 1) := by
  cases objective with
  | false => exact costAccumulatorCalls_encoding a x t s c hc
  | true =>
    have hm := rational_mul_encoding a x
    have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
    simp only [accumulatorCalls, if_true, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [RationalCall.lhs, RationalCall.rhs] <;> omega

theorem oracleCoordinateProgram_trace (a β t ρ sl su : ℚ) (n : ℕ) :
    ((oracleCoordinateProgram n).run (oracleRegisters a β 0 1 t ρ sl su)).2 =
      ((coordinateProgram n).run (coordinateRegisters a β 0 1)).2 ++
      coordinateClipCalls (coordinateInterval a β n).2 ρ := by
  have hf := (coordinateProgram n).run_append (coordinateRegisters a β 0 1)
    [t, ρ, sl, su] (by rw [coordinateProgram_slots]; rfl)
  have htrace := congrArg Prod.snd hf
  have hexec := congrArg Prod.fst hf
  simp only [RationalProgram.run_result, coordinateProgram_exec] at hexec
  rw [oracleCoordinateProgram, RationalProgram.run_seq_trace]
  change ((coordinateProgram n).run (coordinateRegisters a β 0 1 ++ [t, ρ, sl, su])).2 ++
    (coordinateClipProgram.run ((coordinateProgram n).exec
    (coordinateRegisters a β 0 1 ++ [t, ρ, sl, su]))).2 = _
  rw [htrace, hexec]
  rw [show coordinateRegisters a β (coordinateInterval a β n).1
    (coordinateInterval a β n).2 ++ [t, ρ, sl, su] =
      oracleRegisters a β (coordinateInterval a β n).1
        (coordinateInterval a β n).2 t ρ sl su from rfl]
  rw [coordinateClipProgram_trace]

theorem oracleTermProgram_trace (objective : Bool) (a β t ρ sl su : ℚ) (n : ℕ) :
    ((oracleTermProgram objective n).run (oracleRegisters a β 0 1 t ρ sl su)).2 =
      ((coordinateProgram n).run (coordinateRegisters a β 0 1)).2 ++
      coordinateClipCalls (coordinateInterval a β n).2 ρ ++
      accumulatorCalls objective a (oracleCoordinateInterval a β ρ n).1 t sl ++
      accumulatorCalls objective a (oracleCoordinateInterval a β ρ n).2 t su := by
  cases objective <;>
    simp only [oracleTermProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
      RationalProgram.run_seq_trace, RationalProgram.exec,
      Bool.false_eq_true, if_false, if_true, oracleCoordinateProgram_exec,
      budgetAccumulatorProgram_exec, objectiveAccumulatorProgram_exec,
      budgetAccumulatorProgram_trace, objectiveAccumulatorProgram_trace,
      oracleCoordinateProgram_trace, RationalProgram.run, RationalProgram.run_result, List.append_nil,
      accumulatorCalls, List.append_assoc]

theorem oracleTermProgram_operand_encoding (objective : Bool) (a β t ρ sl su : ℚ)
    (n : ℕ) (c : RationalCall)
    (hc : c ∈ ((oracleTermProgram objective n).run (oracleRegisters a β 0 1 t ρ sl su)).2) :
    L c.lhs ≤ 1000 * (L a + L β + L t + L ρ + L sl + L su + n + 1) ∧
      L c.rhs ≤ 1000 * (L a + L β + L t + L ρ + L sl + L su + n + 1) := by
  rw [oracleTermProgram_trace] at hc
  simp only [List.mem_append] at hc
  obtain hi := coordinateInterval_encoding_le a β n
  obtain hj := oracleCoordinateInterval_encoding_le a β ρ n
  rcases hc with ((hc | hc) | hc) | hc
  · have h := coordinateProgram_operand_encoding a β n c hc
    constructor <;> omega
  · have h := coordinateClipCalls_encoding (coordinateInterval a β n).2 ρ c hc
    constructor <;> omega
  · have h := accumulatorCalls_encoding objective a (oracleCoordinateInterval a β ρ n).1 t sl c hc
    constructor <;> omega
  · have h := accumulatorCalls_encoding objective a (oracleCoordinateInterval a β ρ n).2 t su c hc
    constructor <;> omega

end IdentityTesting.RationalComputation
