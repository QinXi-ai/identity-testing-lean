import IdentityTesting.RationalAlgorithmTraceSearchControl

/-! The search controller executes genuine finite-register oracle calls. -/
namespace IdentityTesting.RationalComputation

theorem rationalLiteral_read (q : ℚ) (s : RationalRegisters) :
    (RationalOperand.literal q).read s = q := by rfl

theorem oracleMachine_read0 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 0).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = l := by rfl

theorem oracleMachine_read1 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 1).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = u := by rfl

theorem oracleMachine_read2 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 2).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = ζ := by rfl

theorem oracleMachine_read3 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 3).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = margin := by rfl

theorem oracleMachine_read4 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 4).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = ol := by rfl

theorem oracleMachine_read5 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 5).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = ou := by rfl

theorem oracleMachine_read6 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 6).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = done := by rfl

theorem oracleMachine_read7 {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (RationalOperand.reg 7).read (oracleMachineState a t ρ l u ζ margin ol ou done m) = m := by rfl

theorem oracleMachine_save {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 7 .copy (.reg 4) (.literal 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol ou done ol := by rfl

theorem oracleMachine_restore {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 4 .copy (.reg 7) (.literal 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin m ou done m := by rfl

theorem oracleMachine_done {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 6 .copy (.literal 1) (.literal 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol ou 1 m := by rfl

theorem oracleMachine_subtract {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 4 .sub (.reg 4) (.reg 3)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin (ol - margin) ou done m := by rfl

theorem oracleMachine_addMargin {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 5 .add (.reg 5) (.reg 3)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol (ou + margin) done m := by rfl

theorem oracleMachine_width {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 4 .sub (.reg 1) (.reg 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin (u - l) ou done m := by rfl

theorem oracleMachine_tolerance {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 5 .mul (.reg 2) (.reg 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol (ζ * l) done m := by rfl

theorem oracleMachine_sum {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 7 .add (.reg 0) (.reg 1)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol ou done (l + u) := by rfl

theorem oracleMachine_halve {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 7 .div (.reg 7) (.literal 2)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin ol ou done (m / 2) := by rfl

theorem oracleMachine_upper {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 1 .copy (.reg 7) (.literal 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l m ζ margin ol ou done m := by rfl

theorem oracleMachine_lower {k : ℕ} (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (rationalAssign 0 .copy (.reg 7) (.literal 0)).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ m u ζ margin ol ou done m := by rfl

theorem oracleEvaluateProgram_exec_0 {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleEvaluateProgram objective k n 0).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin
        (oracleIntervalValue objective a t l ρ n).1
        (oracleIntervalValue objective a t l ρ n).2 done m :=
  oracleEvaluateProgram_exec objective n 0 a t ρ l u ζ margin ol ou done m l rfl

theorem oracleEvaluateProgram_exec_1 {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleEvaluateProgram objective k n 1).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin
        (oracleIntervalValue objective a t u ρ n).1
        (oracleIntervalValue objective a t u ρ n).2 done m :=
  oracleEvaluateProgram_exec objective n 1 a t ρ l u ζ margin ol ou done m u rfl

theorem oracleEvaluateProgram_exec_7 {k : ℕ} (objective : Bool) (n : ℕ)
    (a : Fin k → ℚ) (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleEvaluateProgram objective k n 7).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin
        (oracleIntervalValue objective a t m ρ n).1
        (oracleIntervalValue objective a t m ρ n).2 done m :=
  oracleEvaluateProgram_exec objective n 7 a t ρ l u ζ margin ol ou done m m rfl

theorem oracleNarrowProgram_exec {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleNarrowProgram k n).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin
        (oracleObjectiveInterval a l ρ n).1 (oracleObjectiveInterval a u ρ n).2
        1 (oracleObjectiveInterval a l ρ n).1 := by
  simp only [oracleNarrowProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.exec, oracleEvaluateProgram_exec_0, oracleEvaluateProgram_exec_1,
    oracleMachine_save, oracleMachine_restore, oracleMachine_done, oracleIntervalValue, if_true]

theorem oracleAmbiguousProgram_exec {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ l u ζ margin ol ou done m : ℚ) :
    (oracleAmbiguousProgram k n).exec (oracleMachineState a t ρ l u ζ margin ol ou done m) =
      oracleMachineState a t ρ l u ζ margin
        ((oracleObjectiveInterval a m ρ n).1 - margin)
        ((oracleObjectiveInterval a m ρ n).2 + margin) 1 m := by
  simp only [oracleAmbiguousProgram, rationalSequence, List.foldr_cons, List.foldr_nil,
    RationalProgram.exec, oracleEvaluateProgram_exec_7,
    oracleMachine_subtract, oracleMachine_addMargin, oracleMachine_done, oracleIntervalValue, if_true]

theorem oracleSearchFinishProgram_exec {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin : ℚ) (s : OracleSearchControl) :
    (oracleSearchFinishProgram k n).exec (s.registers a t ρ ζ margin) =
      (s.finish (fun β => oracleObjectiveInterval a β ρ n)).registers a t ρ ζ margin := by
  cases hs : s.done <;>
    simp [oracleSearchFinishProgram, OracleSearchControl.registers, hs,
      RationalProgram.exec, oracleMachine_read6, rationalLiteral_read,
      oracleNarrowProgram_exec, OracleSearchControl.finish]

theorem oracleSearchStepProgram_exec {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin : ℚ) (s : OracleSearchControl) :
    (oracleSearchStepProgram k n).exec (s.registers a t ρ ζ margin) =
      (s.step (fun β => oracleBudgetInterval a t β ρ n)
        (fun β => oracleObjectiveInterval a β ρ n) ζ margin).registers a t ρ ζ margin := by
  cases hs : s.done with
  | true => simp [oracleSearchStepProgram, OracleSearchControl.registers, OracleSearchControl.step,
      OracleSearchControl.finish, rationalSequence, RationalProgram.exec, hs,
      oracleMachine_read6, rationalLiteral_read, oracleMachine_width, oracleMachine_tolerance,
      oracleMachine_read4, oracleMachine_read5, oracleNarrowProgram_exec, oracleMachine_sum,
      oracleMachine_halve, oracleEvaluateProgram_exec_7, oracleIntervalValue,
      oracleMachine_lower, oracleMachine_upper, oracleAmbiguousProgram_exec]
  | false =>
    by_cases hn : s.upper - s.lower ≤ ζ * s.lower
    · simp [oracleSearchStepProgram, OracleSearchControl.registers, OracleSearchControl.step,
      OracleSearchControl.finish, rationalSequence, RationalProgram.exec, hs,
      oracleMachine_read6, rationalLiteral_read, oracleMachine_width, oracleMachine_tolerance,
      oracleMachine_read4, oracleMachine_read5, oracleNarrowProgram_exec, oracleMachine_sum,
      oracleMachine_halve, oracleEvaluateProgram_exec_7, oracleIntervalValue,
      oracleMachine_lower, oracleMachine_upper, oracleAmbiguousProgram_exec, hn]
    · by_cases hlo : (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).2 < 1
      · simp [oracleSearchStepProgram, OracleSearchControl.registers, OracleSearchControl.step,
      OracleSearchControl.finish, rationalSequence, RationalProgram.exec, hs,
      oracleMachine_read6, rationalLiteral_read, oracleMachine_width, oracleMachine_tolerance,
      oracleMachine_read4, oracleMachine_read5, oracleNarrowProgram_exec, oracleMachine_sum,
      oracleMachine_halve, oracleEvaluateProgram_exec_7, oracleIntervalValue,
      oracleMachine_lower, oracleMachine_upper, oracleAmbiguousProgram_exec, hn, hlo, not_le.mpr hlo]
      · by_cases hhi : 1 < (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).1
        · simp [oracleSearchStepProgram, OracleSearchControl.registers, OracleSearchControl.step,
      OracleSearchControl.finish, rationalSequence, RationalProgram.exec, hs,
      oracleMachine_read6, rationalLiteral_read, oracleMachine_width, oracleMachine_tolerance,
      oracleMachine_read4, oracleMachine_read5, oracleNarrowProgram_exec, oracleMachine_sum,
      oracleMachine_halve, oracleEvaluateProgram_exec_7, oracleIntervalValue,
      oracleMachine_lower, oracleMachine_upper, oracleAmbiguousProgram_exec, hn, hlo, hhi, not_le.mpr hhi, le_of_not_gt hlo]
        · simp [oracleSearchStepProgram, OracleSearchControl.registers, OracleSearchControl.step,
      OracleSearchControl.finish, rationalSequence, RationalProgram.exec, hs,
      oracleMachine_read6, rationalLiteral_read, oracleMachine_width, oracleMachine_tolerance,
      oracleMachine_read4, oracleMachine_read5, oracleNarrowProgram_exec, oracleMachine_sum,
      oracleMachine_halve, oracleEvaluateProgram_exec_7, oracleIntervalValue,
      oracleMachine_lower, oracleMachine_upper, oracleAmbiguousProgram_exec, hn, hlo, hhi, le_of_not_gt hlo, le_of_not_gt hhi]

end IdentityTesting.RationalComputation
