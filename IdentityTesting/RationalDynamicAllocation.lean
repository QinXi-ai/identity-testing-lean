import IdentityTesting.RationalDynamicSearchTrace

/-! Runtime precision and fuel reproduce the allocation oracle, including its
actual arithmetic trace, when followed by arbitrary scratch registers. -/
namespace IdentityTesting.RationalComputation

set_option maxHeartbeats 1600000

def allocationDynamicSearchInput {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ)
    (scratch : RationalRegisters) : RationalRegisters :=
  allocationOracleSearchInput a t σ ++
    (allocationInnerPrecision a t σ : ℚ) :: (allocationOuterFuel a t σ : ℚ) :: scratch

theorem allocationDynamicSearchInput_precision {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    (RationalOperand.reg (k + 26)).read (allocationDynamicSearchInput a t σ scratch) =
      (allocationInnerPrecision a t σ : ℚ) := by
  have hl : (allocationOracleSearchInput a t σ).length = k + 26 := by
    rw [allocationOracleSearchInput, oracleMachineState_length]; omega
  simp only [allocationDynamicSearchInput, RationalOperand.read,
    List.getElem?_append_right (show (allocationOracleSearchInput a t σ).length ≤ k + 26 by omega), hl,
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem allocationDynamicSearchInput_fuel {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    (RationalOperand.reg (k + 27)).read (allocationDynamicSearchInput a t σ scratch) =
      (allocationOuterFuel a t σ : ℚ) := by
  have hl : (allocationOracleSearchInput a t σ).length = k + 26 := by
    rw [allocationOracleSearchInput, oracleMachineState_length]; omega
  simp only [allocationDynamicSearchInput, RationalOperand.read,
    List.getElem?_append_right (show (allocationOracleSearchInput a t σ).length ≤ k + 27 by omega), hl]
  rw [show k + 27 - (k + 26) = 1 by omega]
  rfl

theorem oracleSearchProgram_slots (k n fuel : ℕ) : (oracleSearchProgram k n fuel).slots ≤ 25 + k :=
  max_le (oracleSearchStepProgram_slots k n) (oracleSearchFinishProgram_slots k n)

theorem allocationDynamicSearchProgram_run_result {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    ((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).run
      (allocationDynamicSearchInput a t σ scratch)).1 =
        ((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
          (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).1 ++
          (allocationInnerPrecision a t σ : ℚ) :: (allocationOuterFuel a t σ : ℚ) :: scratch := by
  rw [oracleDynamicSearchProgram_result _ _ _ _ _ _ (by omega)
    (allocationDynamicSearchInput_precision a t σ scratch) (allocationDynamicSearchInput_fuel a t σ scratch)]
  have h := (oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
    (allocationOuterFuel a t σ)).run_append (allocationOracleSearchInput a t σ)
      ((allocationInnerPrecision a t σ : ℚ) :: (allocationOuterFuel a t σ : ℚ) :: scratch)
      (by rw [allocationOracleSearchInput, oracleMachineState_length]; exact oracleSearchProgram_slots _ _ _)
  simpa only [RationalProgram.run_result] using congrArg Prod.fst h

theorem allocationDynamicSearchProgram_result {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    oracleSearchProgramOutput ((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).run
      (allocationDynamicSearchInput a t σ scratch)).1 = allocationOracle a t σ := by
  rw [allocationDynamicSearchProgram_run_result]
  have hl : (((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
      (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).1).length = 25 + (k + 1) := by
    rw [RationalProgram.run_register_length, allocationOracleSearchInput, oracleMachineState_length]
  unfold oracleSearchProgramOutput
  rw [RationalOperand.read_append _ _ _ (by change 5 ≤ _; omega),
    RationalOperand.read_append _ _ _ (by change 6 ≤ _; omega)]
  exact allocationOracleSearchProgram_result a t σ

theorem allocationDynamicSearchProgram_calls {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (scratch : RationalRegisters) :
    arithmeticCalls ((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).run
      (allocationDynamicSearchInput a t σ scratch)).2 =
        ((oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
          (allocationOuterFuel a t σ)).run (allocationOracleSearchInput a t σ)).2 := by
  rw [oracleDynamicSearchProgram_calls _ _ _ _ _ _ (by omega)
    (allocationDynamicSearchInput_precision a t σ scratch) (allocationDynamicSearchInput_fuel a t σ scratch)]
  have h := (oracleSearchProgram (k + 1) (allocationInnerPrecision a t σ)
    (allocationOuterFuel a t σ)).run_append (allocationOracleSearchInput a t σ)
      ((allocationInnerPrecision a t σ : ℚ) :: (allocationOuterFuel a t σ : ℚ) :: scratch)
      (by rw [allocationOracleSearchInput, oracleMachineState_length]; exact oracleSearchProgram_slots _ _ _)
  simpa only using congrArg Prod.snd h

end IdentityTesting.RationalComputation
