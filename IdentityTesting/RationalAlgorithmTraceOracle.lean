import IdentityTesting.RationalAlgorithmTraceBudgetScalar
import IdentityTesting.RationalInstructionTraceFrames

/-! Composable programs for one actual budget/objective coordinate. -/
namespace IdentityTesting.RationalComputation

def oracleCoordinateProgram (n : ℕ) : RationalProgram :=
  .seq (coordinateProgram n) coordinateClipProgram

theorem oracleCoordinateProgram_exec (a β t ρ sl su : ℚ) (n : ℕ) :
    (oracleCoordinateProgram n).exec (oracleRegisters a β 0 1 t ρ sl su) =
      oracleRegisters a β (oracleCoordinateInterval a β ρ n).1
        (oracleCoordinateInterval a β ρ n).2 t ρ sl su := by
  have h := congrArg Prod.fst ((coordinateProgram n).run_append
    (coordinateRegisters a β 0 1) [t, ρ, sl, su]
    (by rw [coordinateProgram_slots]; rfl))
  simp only [RationalProgram.run_result, coordinateProgram_exec] at h
  change coordinateClipProgram.exec ((coordinateProgram n).exec
    (coordinateRegisters a β 0 1 ++ [t, ρ, sl, su])) = _
  rw [h]
  exact coordinateClipProgram_exec a β (coordinateInterval a β n).1
    (coordinateInterval a β n).2 t ρ sl su

def oracleTermProgram (objective : Bool) (n : ℕ) : RationalProgram :=
  rationalSequence [oracleCoordinateProgram n,
    if objective then objectiveAccumulatorProgram false else budgetAccumulatorProgram false,
    if objective then objectiveAccumulatorProgram true else budgetAccumulatorProgram true]

def oracleTermValue (objective upper : Bool) (a t β ρ : ℚ) (n : ℕ) : ℚ :=
  let I := oracleCoordinateInterval a β ρ n
  let x := if upper then I.2 else I.1
  if objective then a * x else rationalAllocationCost t a x

theorem oracleTermProgram_exec (objective : Bool) (a β t ρ sl su : ℚ) (n : ℕ) :
    (oracleTermProgram objective n).exec (oracleRegisters a β 0 1 t ρ sl su) =
      oracleRegisters a β (oracleCoordinateInterval a β ρ n).1
        (oracleCoordinateInterval a β ρ n).2 t ρ
        (sl + oracleTermValue objective false a t β ρ n)
        (su + oracleTermValue objective true a t β ρ n) := by
  cases objective <;>
    simp only [oracleTermProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
      RationalProgram.exec, Bool.false_eq_true, if_false, if_true,
      oracleCoordinateProgram_exec, budgetAccumulatorProgram_exec,
      objectiveAccumulatorProgram_exec, oracleTermValue]

theorem oracleTermProgram_callBound (objective : Bool) (n : ℕ) :
    (oracleTermProgram objective n).callBound = 21 * n + if objective then 10 else 42 := by
  cases objective <;>
    simp only [oracleTermProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
      RationalProgram.callBound, oracleCoordinateProgram, coordinateProgram,
      coordinateStepProgram_callBound, coordinateClipProgram_callBound,
      budgetAccumulatorProgram_callBound, objectiveAccumulatorProgram_callBound,
      Bool.false_eq_true, if_false, if_true] <;> omega

theorem oracleTermProgram_slots (objective : Bool) (n : ℕ) :
    (oracleTermProgram objective n).slots = 17 := by cases objective <;> rfl

end IdentityTesting.RationalComputation
