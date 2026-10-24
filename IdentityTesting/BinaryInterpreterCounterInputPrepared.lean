import IdentityTesting.BinaryInterpreterCounterInputRuns
import IdentityTesting.RationalPreparedAllocation

/-! The naturalness hypotheses of the counter loader are derived for both
runtime counters produced by the actual raw-input allocation initializer.
This identifies the source-level state; assembling the binary initializer and
the surrounding control dispatcher is a separate obligation. -/
namespace IdentityTesting.BinaryInterpreterCounterInput
open BinaryRationalRegisters RationalComputation

def preparedRegisters {k : ℕ} (a : Fin (k+1) → ℚ) (t σ : ℚ) : RationalRegisters :=
  ((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1

theorem prepared_counter_registers {k : ℕ} (a : Fin (k+1) → ℚ) (t σ : ℚ) :
    2*k+29 < (preparedRegisters a t σ).length ∧
    2*k+30 < (preparedRegisters a t σ).length ∧
    (RationalOperand.reg (2*k+29)).read (preparedRegisters a t σ) = (allocationInnerPrecision a t σ : ℚ) ∧
    (RationalOperand.reg (2*k+30)).read (preparedRegisters a t σ) = (allocationOuterFuel a t σ : ℚ) := by
  let s := preparedRegisters a t σ
  have hblock := oracleInitializerProgram_block a t σ
  change (s.drop (k+3)).take (k+28) = _ at hblock
  have hbase : (allocationOracleSearchInput a t σ).length = k+26 := by
    rw [allocationOracleSearchInput,oracleMachineState_length]
    omega
  have hlen := congrArg List.length hblock
  simp only [List.length_take,List.length_drop,List.length_append,List.length_cons,List.length_nil,hbase] at hlen
  have hprefix : k+3 ≤ s.length := by omega
  let pre := s.take (k+3)
  let rest := (s.drop (k+3)).drop (k+28)
  have hpre : pre.length = k+3 := by simp only [pre,List.length_take]; omega
  have hsuffix : s.drop (k+3) = allocationDynamicSearchInput a t σ rest := by
    simpa only [s,preparedRegisters,rest,allocationDynamicSearchInput,List.append_assoc,List.cons_append,List.nil_append]
      using oracleInitializerProgram_suffix a t σ
  have hsplit : s = pre ++ allocationDynamicSearchInput a t σ rest := by
    rw [← hsuffix]
    exact (List.take_append_drop _ _).symm
  have hp := (RationalOperand.reg (k+26)).shift_read pre (allocationDynamicSearchInput a t σ rest)
  have hf := (RationalOperand.reg (k+27)).shift_read pre (allocationDynamicSearchInput a t σ rest)
  simp only [RationalOperand.shift,hpre] at hp hf
  refine ⟨by change 2*k+29 < s.length; omega,by change 2*k+30 < s.length; omega,?_,?_⟩
  · change (RationalOperand.reg (2*k+29)).read s = _
    rw [show 2*k+29 = k+3+(k+26) by omega,hsplit,hp]
    exact allocationDynamicSearchInput_precision a t σ rest
  · change (RationalOperand.reg (2*k+30)).read s = _
    rw [show 2*k+30 = k+3+(k+27) by omega,hsplit,hf]
    exact allocationDynamicSearchInput_fuel a t σ rest

theorem load_prepared_precision {k : ℕ} (a : Fin (k+1) → ℚ) (t σ : ℚ) :
    ∃ steps,
      let s := preparedRegisters a t σ
      advance steps (initial (tape s) (List.replicate (2*k+29) false)) =
        haltState (tape s) (allocationInnerPrecision a t σ).bits ∧
      bitSteps steps (initial (tape s) (List.replicate (2*k+29) false)) ≤
        45*(rationalRegisterEncoding s+s.length)+30*rationalEncodingLength (allocationInnerPrecision a t σ : ℚ)+180 := by
  have h := prepared_counter_registers a t σ
  obtain ⟨steps,_,he,hc⟩ := binary_natural_counter_load (preparedRegisters a t σ) (2*k+29)
    h.1 (allocationInnerPrecision a t σ) h.2.2.1
  exact ⟨steps,he,hc⟩

theorem load_prepared_fuel {k : ℕ} (a : Fin (k+1) → ℚ) (t σ : ℚ) :
    ∃ steps,
      let s := preparedRegisters a t σ
      advance steps (initial (tape s) (List.replicate (2*k+30) false)) =
        haltState (tape s) (allocationOuterFuel a t σ).bits ∧
      bitSteps steps (initial (tape s) (List.replicate (2*k+30) false)) ≤
        45*(rationalRegisterEncoding s+s.length)+30*rationalEncodingLength (allocationOuterFuel a t σ : ℚ)+180 := by
  have h := prepared_counter_registers a t σ
  obtain ⟨steps,_,he,hc⟩ := binary_natural_counter_load (preparedRegisters a t σ) (2*k+30)
    h.2.1 (allocationOuterFuel a t σ) h.2.2.2
  exact ⟨steps,he,hc⟩

end IdentityTesting.BinaryInterpreterCounterInput
