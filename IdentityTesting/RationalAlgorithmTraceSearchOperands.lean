import IdentityTesting.RationalAlgorithmTraceSearchStepOperands
import IdentityTesting.RationalAlgorithmTraceSearchGrid
import IdentityTesting.RationalAlgorithmTraceSearchResult

/-! A polynomial bound for every actual search operand, including comparisons
and the final fuel-exhaustion objective evaluations. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def oracleSearchTraceSize {k : ℕ} (a : Fin k → ℚ) (t ρ ζ margin b B : ℚ)
    (n fuel : ℕ) : ℕ :=
  rationalVectorEncodingLength a + L t + L ρ + L ζ + L margin +
    2 * (6 * L b + 4 * L B + 4 * fuel + 9) + n + 1

theorem oracleSearchFinishProgram_operand_encoding {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin : ℚ) (s : OracleSearchControl) (c : RationalCall)
    (hc : c ∈ ((oracleSearchFinishProgram k n).run (s.registers a t ρ ζ margin)).2) :
    L c.lhs ≤ 20000000 * (k + 1) * oracleControlSize a t ρ ζ margin s.lower s.upper n ∧
      L c.rhs ≤ 20000000 * (k + 1) * oracleControlSize a t ρ ζ margin s.lower s.upper n := by
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have hscale : 1 ≤ oracleControlSize a t ρ ζ margin s.lower s.upper n := by
    unfold oracleControlSize; omega
  cases hs : s.done with
  | true =>
    simp only [oracleSearchFinishProgram, OracleSearchControl.registers, hs, if_true,
      RationalProgram.run_branch_trace, oracleMachine_read6, rationalLiteral_read] at hc
    norm_num [rationalSkip_run_trace] at hc
    subst c
    simp only [RationalCall.lhs, RationalCall.rhs]
    constructor <;> nlinarith
  | false =>
    simp only [oracleSearchFinishProgram, OracleSearchControl.registers, hs, Bool.false_eq_true,
      if_false, RationalProgram.run_branch_trace, oracleMachine_read6, rationalLiteral_read,
      le_refl, if_true, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [RationalCall.lhs, RationalCall.rhs]
      constructor <;> nlinarith
    · have h := oracleNarrowProgram_operand_encoding n a t ρ s.lower s.upper ζ margin
        s.outLower s.outUpper 0 s.middle c hc
      constructor <;> nlinarith [h.1, h.2]

theorem oracleSearchProgram_operand_encoding {k : ℕ} (n fuel : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin b B : ℚ) (c : RationalCall)
    (hc : c ∈ ((oracleSearchProgram k n fuel).run
      (oracleMachineState a t ρ b B ζ margin 0 0 0 0)).2) :
    L c.lhs ≤ 20000000 * (k + 1) * oracleSearchTraceSize a t ρ ζ margin b B n fuel ∧
      L c.rhs ≤ 20000000 * (k + 1) * oracleSearchTraceSize a t ρ ζ margin b B n fuel := by
  let s : OracleSearchControl := ⟨b, B, 0, 0, 0, false⟩
  let budget := fun β => oracleBudgetInterval a t β ρ n
  let objective := fun β => oracleObjectiveInterval a β ρ n
  have hgrid := OracleSearchControl.initial_grid b B
  have hsize (i : ℕ) (hi : i ≤ fuel) :
      oracleControlSize a t ρ ζ margin
        (OracleSearchControl.loop budget objective ζ margin i s).lower
        (OracleSearchControl.loop budget objective ζ margin i s).upper n ≤
      oracleSearchTraceSize a t ρ ζ margin b B n fuel := by
    have hg := OracleSearchControl.loop_grid budget objective ζ margin b B i 0 s hgrid
    have he := OracleSearchControl.grid_encoding b B (0 + i) _ hg
    unfold oracleControlSize oracleSearchTraceSize
    omega
  change c ∈ ((oracleSearchProgram k n fuel).run (s.registers a t ρ ζ margin)).2 at hc
  rw [oracleSearchProgram, RationalProgram.run_seq_trace] at hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, hi, hc⟩ := traceIterate_mem (oracleSearchStepProgram k n).run
      (oracleSearchStepProgram k n).exec (oracleSearchStepProgram k n).run_result
      fuel (s.registers a t ρ ζ margin) c hc
    rw [oracleSearchLoop_exec] at hc
    have h := oracleSearchStepProgram_operand_encoding n a t ρ ζ margin
      (OracleSearchControl.loop budget objective ζ margin i s) c hc
    have hm := Nat.mul_le_mul_left (20000000 * (k + 1)) (hsize i hi.le)
    exact ⟨h.1.trans hm, h.2.trans hm⟩
  · change c ∈ ((oracleSearchFinishProgram k n).run
      (registerIterate (oracleSearchStepProgram k n).exec fuel (s.registers a t ρ ζ margin))).2 at hc
    rw [oracleSearchLoop_exec] at hc
    have h := oracleSearchFinishProgram_operand_encoding n a t ρ ζ margin
      (OracleSearchControl.loop budget objective ζ margin fuel s) c hc
    have hm := Nat.mul_le_mul_left (20000000 * (k + 1)) (hsize fuel le_rfl)
    exact ⟨h.1.trans hm, h.2.trans hm⟩

end IdentityTesting.RationalComputation
