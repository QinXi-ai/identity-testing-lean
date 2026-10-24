import IdentityTesting.BinaryInterpreterCeilSizeLayout

namespace IdentityTesting.BinaryInterpreterCeilSize
open BinaryInterpreterLayout BinaryInterpreterArithmetic BinaryRationalRegisters RationalComputation
open BinaryWorkspaceAdapters

theorem result_encoding (q : ℚ) :
    rationalEncodingLength ((Nat.ceil q).size : ℚ) ≤ 8001 * (rationalEncodingLength q + 1)^2 := by
  obtain ⟨n, _, ho, hc⟩ := BinaryRationalArithmeticCeilSize.binary_rational_ceilSize_machine q
  let s := BinaryRationalArithmeticCeilSize.initial (BinaryRationalArithmetic.encode q)
  let f := BinaryRationalArithmeticCeilSize.advance n s
  have hg := rationalCeilSize_cells_cost n s
  have hi := rationalCeilSize_initial_cells (BinaryRationalArithmetic.encode q)
  rw [BinaryRationalArithmetic.encode_length] at hi
  have hf := rationalCeilSizeScratch_cells f
  have hout := congrArg BinaryRationalArithmetic.Word.length ho
  rw [BinaryRationalArithmetic.encode_length] at hout
  change 1 + f.measure.norm.out.length + f.denominator.length =
    rationalEncodingLength ((Nat.ceil q).size : ℚ) at hout
  change rationalCeilSizeCells s + 1 = rationalEncodingLength q at hi
  change rationalCeilSizeCells f ≤ rationalCeilSizeCells s +
    BinaryRationalArithmeticCeilSize.bitSteps n s at hg
  change BinaryRationalArithmeticCeilSize.bitSteps n s ≤ _ at hc
  have hz : rationalEncodingLength ((Nat.ceil q).size : ℚ) ≤
      rationalEncodingLength q + BinaryRationalArithmeticCeilSize.bitSteps n s := by omega
  have hq : rationalEncodingLength q ≤ (rationalEncodingLength q + 1)^2 := by nlinarith
  omega

/-- A ceiling-size control event loads the source, executes the actual primitive,
and writes the result to the shared register tape. Source and destination may
alias. Unary addresses are supplied on the input stacks. -/
theorem binary_register_ceilSize (s : RationalRegisters) (a dst : ℕ)
    (ha : a < s.length) (hd : dst < s.length) :
    ∃ n,
      let start := initial layout (tape s)
        (List.replicate a false) (List.replicate a false) (List.replicate dst false)
      (advance n start).phase = .halt ∧
      (advance n start).tape = tape (s.set dst ((Nat.ceil s[a]).size : ℚ)) ∧
      CleanIO (advance n start) ∧
      bitSteps n start ≤ 300 * (rationalRegisterEncoding s + s.length) +
        1100000 * (rationalEncodingLength s[a] + 1)^2 := by
  obtain ⟨nm, hm, hz, hcost⟩ := local_run s[a] s[a]
  obtain ⟨n, hh, ht, hi, hc⟩ := load_operate_store layout s a a dst ha ha hd nm
    ((Nat.ceil s[a]).size : ℚ) hm hz
  refine ⟨n, hh, ht, hi, ?_⟩
  have hout := result_encoding s[a]
  nlinarith only [hc, hcost, hout]

end IdentityTesting.BinaryInterpreterCeilSize
