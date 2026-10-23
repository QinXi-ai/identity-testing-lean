import IdentityTesting.RationalAlgorithmTraceSearchOperandMacros

/-! All operands executed by one actual search-control step. -/
namespace IdentityTesting.RationalComputation
set_option maxHeartbeats 1600000
local notation "L" => rationalEncodingLength

theorem RationalProgram.run_branch_trace (a b : RationalOperand) (p q : RationalProgram)
    (s : RationalRegisters) :
    ((.branchLe a b p q : RationalProgram).run s).2 =
      ⟨.le, a.read s, b.read s⟩ ::
        (if a.read s ≤ b.read s then (p.run s).2 else (q.run s).2) := by
  simp only [run, RationalCall.result, RationalOp.eval]
  split <;> simp_all

theorem rationalAssign_run_trace (i : ℕ) (op : RationalOp) (a b : RationalOperand)
    (s : RationalRegisters) :
    ((rationalAssign i op a b).run s).2 = [⟨op, a.read s, b.read s⟩] := by rfl

theorem rationalSkip_run_trace (s : RationalRegisters) : (RationalProgram.skip.run s).2 = [] := by rfl

theorem oracleSearchStepProgram_operand_encoding {k : ℕ} (n : ℕ) (a : Fin k → ℚ)
    (t ρ ζ margin : ℚ) (s : OracleSearchControl) (c : RationalCall)
    (hc : c ∈ ((oracleSearchStepProgram k n).run (s.registers a t ρ ζ margin)).2) :
    L c.lhs ≤ 20000000 * (k + 1) * oracleControlSize a t ρ ζ margin s.lower s.upper n ∧
      L c.rhs ≤ 20000000 * (k + 1) * oracleControlSize a t ρ ζ margin s.lower s.upper n := by
  let X := oracleControlSize a t ρ ζ margin s.lower s.upper n
  let m := (s.lower + s.upper) / 2
  have hX : 1 ≤ X := by dsimp [X, oracleControlSize]; omega
  have hmargin : L margin ≤ X := by dsimp [X, oracleControlSize]; omega
  have hsum := rational_add_encoding s.lower s.upper
  have hmid := rational_div_encoding_le (s.lower + s.upper) 2
  have hdiff := rational_sub_encoding s.upper s.lower
  have hmul := rational_mul_encoding ζ s.lower
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have htwo : L 2 = 4 := by
    have hs : Nat.size 2 = 2 := Nat.size_pow (n := 1)
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits, hs]
  have hb : oracleTraceSize a m t ρ n ≤ 8 * X := by
    dsimp [m, X, oracleTraceSize, oracleControlSize] at *
    omega
  have hQ := oracleIntervalValue_encoding false n a t m ρ
  simp only [oracleIntervalValue, Bool.false_eq_true, if_false] at hQ
  have hbmul := Nat.mul_le_mul_left (1000000 * (k + 1)) hb
  have heval (ol ou done : ℚ) (c : RationalCall)
      (hc : c ∈ ((oracleEvaluateProgram false k n 7).run
        (oracleMachineState a t ρ s.lower s.upper ζ margin ol ou done m)).2) :
      L c.lhs ≤ 20000000 * (k + 1) * X ∧ L c.rhs ≤ 20000000 * (k + 1) * X := by
    have h := oracleEvaluateProgram_operand_encoding false n 7 a t ρ s.lower s.upper ζ margin ol ou done m m rfl c hc
    constructor <;> nlinarith only [h.1, h.2, hbmul]
  have hamb (ol ou done : ℚ) (c : RationalCall)
      (hc : c ∈ ((oracleAmbiguousProgram k n).run
        (oracleMachineState a t ρ s.lower s.upper ζ margin ol ou done m)).2) :
      L c.lhs ≤ 20000000 * (k + 1) * X ∧ L c.rhs ≤ 20000000 * (k + 1) * X := by
    have h := oracleAmbiguousProgram_operand_encoding n a t ρ s.lower s.upper ζ margin ol ou done m c hc
    have hh : oracleTraceSize a m t ρ n + L margin ≤ 9 * X := by omega
    have hm := Nat.mul_le_mul_left (1000000 * (k + 1)) hh
    constructor <;> nlinarith only [h.1, h.2, hm]
  have hnarrow (ol ou done middle : ℚ) (c : RationalCall)
      (hc : c ∈ ((oracleNarrowProgram k n).run
        (oracleMachineState a t ρ s.lower s.upper ζ margin ol ou done middle)).2) :
      L c.lhs ≤ 20000000 * (k + 1) * X ∧ L c.rhs ≤ 20000000 * (k + 1) * X := by
    have h := oracleNarrowProgram_operand_encoding n a t ρ s.lower s.upper ζ margin ol ou done middle c hc
    change _ ≤ 1000000 * (k + 1) * X ∧ _ ≤ 1000000 * (k + 1) * X at h
    constructor <;> nlinarith only [h.1, h.2]
  have hprim (c : RationalCall)
      (hc : c ∈ [⟨.le, 0, 0⟩, ⟨.le, 1, 0⟩, ⟨.sub, s.upper, s.lower⟩,
        ⟨.mul, ζ, s.lower⟩, ⟨.le, s.upper - s.lower, ζ * s.lower⟩,
        ⟨.add, s.lower, s.upper⟩, ⟨.div, s.lower + s.upper, 2⟩,
        ⟨.le, 1, (oracleBudgetInterval a t m ρ n).2⟩,
        ⟨.le, (oracleBudgetInterval a t m ρ n).1, 1⟩, ⟨.copy, m, 0⟩]) :
      L c.lhs ≤ 20000000 * (k + 1) * X ∧ L c.rhs ≤ 20000000 * (k + 1) * X := by
    have hl : L s.lower ≤ X := by dsimp [X, oracleControlSize]; omega
    have hu : L s.upper ≤ X := by dsimp [X, oracleControlSize]; omega
    have hζ : L ζ ≤ X := by dsimp [X, oracleControlSize]; omega
    have hm : L m ≤ 4 * X + 5 := by dsimp [m]; omega
    have hbase : 20000000 * X ≤ 20000000 * (k + 1) * X :=
      Nat.mul_le_mul_right X (by omega)
    have hscaleQ := Nat.mul_le_mul_left (400 * k) hb
    have hql : L (oracleBudgetInterval a t m ρ n).1 ≤ 20000000 * (k + 1) * X := by
      nlinarith only [hQ.1, hscaleQ, hX, hbase]
    have hqu : L (oracleBudgetInterval a t m ρ n).2 ≤ 20000000 * (k + 1) * X := by
      nlinarith only [hQ.2, hscaleQ, hX, hbase]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [RationalCall.lhs, RationalCall.rhs] <;> constructor <;>
      omega
  change L c.lhs ≤ 20000000 * (k + 1) * X ∧ L c.rhs ≤ 20000000 * (k + 1) * X
  cases hs : s.done with
  | true =>
    simp only [oracleSearchStepProgram, OracleSearchControl.registers, hs,
      Bool.false_eq_true, if_false, if_true, RationalProgram.run_branch_trace,
      rationalSequence, List.foldr_cons, List.foldr_nil, RationalProgram.run_seq_trace,
      RationalProgram.exec, rationalAssign_run_trace, rationalSkip_run_trace,
      oracleMachine_width, oracleMachine_tolerance, oracleMachine_sum, oracleMachine_halve,
      oracleEvaluateProgram_exec_7, oracleIntervalValue, oracleMachine_read4,
      oracleMachine_read0, oracleMachine_read1, oracleMachine_read2, oracleMachine_read3,
      oracleMachine_read5, oracleMachine_read6, oracleMachine_read7, rationalLiteral_read,
      RationalProgram.run_result, le_refl, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, List.append_nil] at hc
    norm_num at hc
    subst c
    exact hprim _ (by simp)
  | false =>
    by_cases hn : s.upper - s.lower ≤ ζ * s.lower
    · simp only [oracleSearchStepProgram, OracleSearchControl.registers, hs,
      Bool.false_eq_true, if_false, if_true, RationalProgram.run_branch_trace,
      rationalSequence, List.foldr_cons, List.foldr_nil, RationalProgram.run_seq_trace,
      RationalProgram.exec, rationalAssign_run_trace, rationalSkip_run_trace,
      oracleMachine_width, oracleMachine_tolerance, oracleMachine_sum, oracleMachine_halve,
      oracleEvaluateProgram_exec_7, oracleIntervalValue, oracleMachine_read4,
      oracleMachine_read0, oracleMachine_read1, oracleMachine_read2, oracleMachine_read3,
      oracleMachine_read5, oracleMachine_read6, oracleMachine_read7, rationalLiteral_read,
      RationalProgram.run_result, le_refl, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, List.append_nil, if_pos hn] at hc
      rcases hc with rfl | rfl | rfl | rfl | hc
      · exact hprim _ (by simp)
      · exact hprim _ (by simp)
      · exact hprim _ (by simp)
      · exact hprim _ (by simp)
      · exact hnarrow _ _ _ _ c hc
    · by_cases hlo : (oracleBudgetInterval a t m ρ n).2 < 1
      · dsimp only [m] at hlo
        simp only [oracleSearchStepProgram, OracleSearchControl.registers, hs,
      Bool.false_eq_true, if_false, if_true, RationalProgram.run_branch_trace,
      rationalSequence, List.foldr_cons, List.foldr_nil, RationalProgram.run_seq_trace,
      RationalProgram.exec, rationalAssign_run_trace, rationalSkip_run_trace,
      oracleMachine_width, oracleMachine_tolerance, oracleMachine_sum, oracleMachine_halve,
      oracleEvaluateProgram_exec_7, oracleIntervalValue, oracleMachine_read4,
      oracleMachine_read0, oracleMachine_read1, oracleMachine_read2, oracleMachine_read3,
      oracleMachine_read5, oracleMachine_read6, oracleMachine_read7, rationalLiteral_read,
      RationalProgram.run_result, le_refl, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, List.append_nil, if_neg hn, show ¬ (1 : ℚ) ≤ (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).2 from not_le.mpr hlo, if_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hc | rfl | rfl
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
        · exact heval _ _ _ c hc
        · exact hprim _ (by simp [m])
        · exact hprim _ (by simp [m])
      · by_cases hhi : 1 < (oracleBudgetInterval a t m ρ n).1
        · dsimp only [m] at hlo hhi
          simp only [oracleSearchStepProgram, OracleSearchControl.registers, hs,
      Bool.false_eq_true, if_false, if_true, RationalProgram.run_branch_trace,
      rationalSequence, List.foldr_cons, List.foldr_nil, RationalProgram.run_seq_trace,
      RationalProgram.exec, rationalAssign_run_trace, rationalSkip_run_trace,
      oracleMachine_width, oracleMachine_tolerance, oracleMachine_sum, oracleMachine_halve,
      oracleEvaluateProgram_exec_7, oracleIntervalValue, oracleMachine_read4,
      oracleMachine_read0, oracleMachine_read1, oracleMachine_read2, oracleMachine_read3,
      oracleMachine_read5, oracleMachine_read6, oracleMachine_read7, rationalLiteral_read,
      RationalProgram.run_result, le_refl, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, List.append_nil, if_neg hn, show (1 : ℚ) ≤ (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).2 from le_of_not_gt hlo,
            show ¬ (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).1 ≤ 1 from not_le.mpr hhi, if_false, if_true] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hc | rfl | rfl | rfl
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact heval _ _ _ c hc
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
        · dsimp only [m] at hlo hhi
          simp only [oracleSearchStepProgram, OracleSearchControl.registers, hs,
      Bool.false_eq_true, if_false, if_true, RationalProgram.run_branch_trace,
      rationalSequence, List.foldr_cons, List.foldr_nil, RationalProgram.run_seq_trace,
      RationalProgram.exec, rationalAssign_run_trace, rationalSkip_run_trace,
      oracleMachine_width, oracleMachine_tolerance, oracleMachine_sum, oracleMachine_halve,
      oracleEvaluateProgram_exec_7, oracleIntervalValue, oracleMachine_read4,
      oracleMachine_read0, oracleMachine_read1, oracleMachine_read2, oracleMachine_read3,
      oracleMachine_read5, oracleMachine_read6, oracleMachine_read7, rationalLiteral_read,
      RationalProgram.run_result, le_refl, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc, List.append_nil, if_neg hn, show (1 : ℚ) ≤ (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).2 from le_of_not_gt hlo,
            show (oracleBudgetInterval a t ((s.lower + s.upper) / 2) ρ n).1 ≤ 1 from le_of_not_gt hhi, if_true] at hc
          rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | hc | rfl | rfl | hc
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact heval _ _ _ c hc
          · exact hprim _ (by simp [m])
          · exact hprim _ (by simp [m])
          · exact hamb _ _ _ c hc

end IdentityTesting.RationalComputation
