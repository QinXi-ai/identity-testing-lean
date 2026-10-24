import IdentityTesting.RationalDynamicCodeBounds
import IdentityTesting.RationalDynamicSearch
import IdentityTesting.RationalAlgorithmTraceSearchCodeSize

/-! The serialized search code has a polynomial bound independent of runtime
precision and fuel. Only the dimension and chosen register addresses occur. -/
namespace IdentityTesting.RationalComputation

theorem oracleDynamicSearchProgram_slots (k i j : ℕ) :
    (oracleDynamicSearchProgram k i j).slots ≤ 25 + k + i + j + 2 := by
  have hs := (oracleSearchStepProgram k 0).dynamicRepeats_slots i
  have hf := (oracleSearchFinishProgram k 0).dynamicRepeats_slots i
  have hss := oracleSearchStepProgram_slots k 0
  have hfs := oracleSearchFinishProgram_slots k 0
  simp only [oracleDynamicSearchProgram, RationalControlProgram.slots]
  omega

theorem oracleDynamicSearchProgram_encoding (k i j : ℕ) :
    (oracleDynamicSearchProgram k i j).encoding ≤
      (i + j + 2) * (200 * (k * (k + 40001) + 1) + 10000) := by
  have hs := (oracleSearchStepProgram k 0).dynamicRepeats_encoding i
  have hf := (oracleSearchFinishProgram k 0).dynamicRepeats_encoding i
  have hstatic := oracleSearchProgram_encoding k 0 0
  have hi : i.size ≤ i := Nat.size_le.mpr i.lt_two_pow_self
  have hj : j.size ≤ j := Nat.size_le.mpr j.lt_two_pow_self
  have hbase : (oracleDynamicSearchProgram k i j).encoding ≤
      (i + j + 2) * (oracleSearchProgram k 0 0).encoding := by
    simp only [oracleDynamicSearchProgram, RationalControlProgram.encoding,
      oracleSearchProgram, RationalProgram.encoding, Nat.size_zero]
    nlinarith
  exact hbase.trans (Nat.mul_le_mul_left _ (by simpa using hstatic))

theorem oracleDynamicSearchProgram_tape_length (k i j : ℕ) :
    (RationalProgramCode.control (oracleDynamicSearchProgram k i j)).length ≤
      30 * (25 + k + i + j + 3) *
        ((i + j + 2) * (200 * (k * (k + 40001) + 1) + 10000)) := by
  exact (RationalProgramCode.control_length_le _ _ (oracleDynamicSearchProgram_slots k i j)).trans
    (Nat.mul_le_mul_left _ (oracleDynamicSearchProgram_encoding k i j))

end IdentityTesting.RationalComputation
