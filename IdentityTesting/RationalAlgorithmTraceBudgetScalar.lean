import IdentityTesting.RationalAlgorithmTraceCoordinate

/-! Explicit arithmetic programs for clipping coordinates and accumulating the
original budget and objective. Every power is expanded into multiplications. -/
namespace IdentityTesting.RationalComputation

def allocationCostProgram : RationalProgram := rationalSequence [
  rationalAssign 5 .mul (.reg 4) (.reg 4),
  rationalAssign 6 .mul (.reg 5) (.reg 5),
  rationalAssign 7 .mul (.reg 13) (.reg 13),
  rationalAssign 8 .mul (.reg 0) (.reg 0),
  rationalAssign 9 .mul (.reg 7) (.reg 8),
  rationalAssign 10 .mul (.reg 9) (.reg 6),
  rationalAssign 11 .sub (.literal 1) (.reg 6),
  rationalAssign 12 .div (.reg 10) (.reg 11)]

def budgetAccumulatorProgram (upper : Bool) : RationalProgram := rationalSequence [
  rationalAssign 4 .copy (.reg (if upper then 3 else 2)) (.literal 0),
  allocationCostProgram,
  rationalAssign (if upper then 16 else 15) .add
    (.reg (if upper then 16 else 15)) (.reg 12),
  coordinateClearProgram]

def oracleRegisters (a β l u t ρ sl su : ℚ) : RationalRegisters :=
  coordinateRegisters a β l u ++ [t, ρ, sl, su]

theorem budgetAccumulatorProgram_exec (upper : Bool) (a β l u t ρ sl su : ℚ) :
    (budgetAccumulatorProgram upper).exec (oracleRegisters a β l u t ρ sl su) =
      if upper then oracleRegisters a β l u t ρ sl (su + rationalAllocationCost t a u)
      else oracleRegisters a β l u t ρ (sl + rationalAllocationCost t a l) su := by
  cases upper <;>
    simp [budgetAccumulatorProgram, allocationCostProgram, coordinateClearProgram,
      rationalSequence, rationalAssign, oracleRegisters, coordinateRegisters,
      RationalProgram.exec, RationalInstruction.exec, RationalInstruction.call,
      RationalOperand.read, RationalCall.result, RationalOp.eval,
      rationalAllocationCost, pow_succ, mul_assoc]

def objectiveAccumulatorProgram (upper : Bool) : RationalProgram := rationalSequence [
  rationalAssign 4 .mul (.reg 0) (.reg (if upper then 3 else 2)),
  rationalAssign (if upper then 16 else 15) .add
    (.reg (if upper then 16 else 15)) (.reg 4),
  rationalAssign 4 .copy (.literal 0) (.literal 0)]

theorem objectiveAccumulatorProgram_exec (upper : Bool) (a β l u t ρ sl su : ℚ) :
    (objectiveAccumulatorProgram upper).exec (oracleRegisters a β l u t ρ sl su) =
      if upper then oracleRegisters a β l u t ρ sl (su + a * u)
      else oracleRegisters a β l u t ρ (sl + a * l) su := by
  cases upper <;>
    simp [objectiveAccumulatorProgram, rationalSequence, rationalAssign, oracleRegisters,
      coordinateRegisters, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalOperand.read, RationalCall.result, RationalOp.eval]

def coordinateClipProgram : RationalProgram := rationalSequence [
  rationalAssign 4 .sub (.literal 1) (.reg 14),
  .branchLe (.reg 3) (.reg 4) .skip (rationalAssign 3 .copy (.reg 4) (.literal 0)),
  rationalAssign 4 .copy (.literal 0) (.literal 0)]

theorem coordinateClipProgram_exec (a β l u t ρ sl su : ℚ) :
    coordinateClipProgram.exec (oracleRegisters a β l u t ρ sl su) =
      oracleRegisters a β l (min u (1 - ρ)) t ρ sl su := by
  simp [coordinateClipProgram, rationalSequence, rationalAssign, oracleRegisters,
    coordinateRegisters, RationalProgram.exec, RationalInstruction.exec,
    RationalInstruction.call, RationalOperand.read, RationalCall.result, RationalOp.eval,
    min_def]
  split <;> simp_all

theorem budgetAccumulatorProgram_callBound (upper : Bool) :
    (budgetAccumulatorProgram upper).callBound = 19 := by cases upper <;> rfl

theorem objectiveAccumulatorProgram_callBound (upper : Bool) :
    (objectiveAccumulatorProgram upper).callBound = 3 := by cases upper <;> rfl

theorem coordinateClipProgram_callBound : coordinateClipProgram.callBound = 4 := by rfl

end IdentityTesting.RationalComputation
