import IdentityTesting.RationalOracleInitializerProgram
import IdentityTesting.RationalDynamicAllocation
import IdentityTesting.RationalDynamicRelocation

/-! The actual raw-input initializer followed by runtime-controlled allocation
search. Only the dimension occurs in the program syntax; all rational input
data, precision and loop fuel are read or computed during execution. -/
namespace IdentityTesting.RationalComputation

set_option maxHeartbeats 1600000

def preparedAllocationProgram (k : ℕ) : RationalControlProgram :=
  .seq (oracleInitializerProgram k)
    ((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).shift (k + 3))

def preparedAllocationOutput (k : ℕ) (s : RationalRegisters) : ℚ × ℚ :=
  ((RationalOperand.reg (k + 7)).read s, (RationalOperand.reg (k + 8)).read s)

theorem preparedAllocationProgram_result {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    preparedAllocationOutput k
      (((preparedAllocationProgram k).run (oracleInitializerInput a t σ)).1) = allocationOracle a t σ := by
  let initialized := ((oracleInitializerProgram k).run (oracleInitializerInput a t σ)).1
  let pre := initialized.take (k + 3)
  let tail := (initialized.drop (k + 3)).drop (k + 28)
  have hlen : k + 3 ≤ initialized.length := by
    dsimp only [initialized]
    rw [RationalControlProgram.run_result, RationalControlProgram.exec_length, oracleInitializerInput_length]
    omega
  have hpre : pre.length = k + 3 := by simp only [pre, List.length_take]; omega
  have hsuffix : initialized.drop (k + 3) = allocationDynamicSearchInput a t σ tail := by
    simpa only [initialized, tail, allocationDynamicSearchInput, List.append_assoc,
      List.cons_append, List.nil_append] using oracleInitializerProgram_suffix a t σ
  have hsplit : initialized = pre ++ allocationDynamicSearchInput a t σ tail := by
    rw [← hsuffix]
    exact (List.take_append_drop _ _).symm
  have hr := (oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).shift_run pre
    (allocationDynamicSearchInput a t σ tail)
  rw [hpre] at hr
  change preparedAllocationOutput k
    (((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).shift (k + 3)).run initialized).1 = _
  rw [hsplit, hr]
  have h4 := (RationalOperand.reg 4).shift_read pre
    (((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).run
      (allocationDynamicSearchInput a t σ tail)).1)
  have h5 := (RationalOperand.reg 5).shift_read pre
    (((oracleDynamicSearchProgram (k + 1) (k + 26) (k + 27)).run
      (allocationDynamicSearchInput a t σ tail)).1)
  simp only [RationalOperand.shift, hpre] at h4 h5
  simp only [preparedAllocationOutput]
  rw [show k + 7 = k + 3 + 4 by omega, show k + 8 = k + 3 + 5 by omega, h4, h5]
  exact allocationDynamicSearchProgram_result a t σ tail

end IdentityTesting.RationalComputation
