import IdentityTesting.RationalAlgorithmTraceCoordinate

/-! Bounds for every actually executed operand, including branch comparisons
and intermediate products, in the finite-register coordinate program. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def coordinateStepCalls (a β l u : ℚ) : List RationalCall :=
  let m := (l + u) / 2
  [⟨.add, l, u⟩, ⟨.div, l + u, 2⟩,
   ⟨.mul, m, m⟩, ⟨.mul, m ^ 2, m⟩, ⟨.mul, m ^ 2, m ^ 2⟩,
   ⟨.sub, 1, m ^ 4⟩, ⟨.mul, 1 - m ^ 4, 1 - m ^ 4⟩,
   ⟨.mul, a, m ^ 3⟩, ⟨.mul, β, (1 - m ^ 4) ^ 2⟩,
   ⟨.sub, a * m ^ 3, β * (1 - m ^ 4) ^ 2⟩,
   ⟨.le, coordinatePolynomial a β m, 0⟩, ⟨.copy, m, 0⟩] ++
    List.replicate 9 ⟨.copy, 0, 0⟩

theorem coordinateStepProgram_trace (a β l u : ℚ) :
    (coordinateStepProgram.run (coordinateRegisters a β l u)).2 = coordinateStepCalls a β l u := by
  simp [coordinateStepProgram, coordinatePolynomialProgram, coordinateClearProgram,
    rationalSequence, rationalAssign, coordinateRegisters, RationalProgram.run,
    RationalInstruction.exec, RationalInstruction.call, RationalOperand.read,
    RationalCall.result, RationalOp.eval, coordinateStepCalls,
    coordinatePolynomial, pow_succ, mul_assoc]
  split <;> simp_all

theorem coordinateStep_operand_encoding (a β : ℚ) (i : ℕ) (c : RationalCall)
    (hc : c ∈ (coordinateStepProgram.run (coordinateRegisters a β
      (coordinateInterval a β i).1 (coordinateInterval a β i).2)).2) :
    L c.lhs ≤ 2 * (L a + L β) + 76 * i + 255 ∧
      L c.rhs ≤ 2 * (L a + L β) + 76 * i + 255 := by
  rw [coordinateStepProgram_trace] at hc
  have hI := coordinateInterval_encoding_le a β i
  have hsum := rational_add_encoding (coordinateInterval a β i).1 (coordinateInterval a β i).2
  have hm := coordinateQuery_encoding_le a β i
  have h2 := rational_pow_encoding (coordinateQuery a β i) 2
  have h3 := rational_pow_encoding (coordinateQuery a β i) 3
  have h4 := rational_pow_encoding (coordinateQuery a β i) 4
  have hd := rational_sub_encoding 1 ((coordinateQuery a β i) ^ 4)
  have hdd := rational_pow_encoding (1 - (coordinateQuery a β i) ^ 4) 2
  have ham := rational_mul_encoding a ((coordinateQuery a β i) ^ 3)
  have hbm := rational_mul_encoding β ((1 - (coordinateQuery a β i) ^ 4) ^ 2)
  have hp := coordinateQuery_polynomial_encoding_le a β i
  have hzero : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have hone : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  have htwo : L 2 = 4 := by
    have hs : Nat.size 2 = 2 := Nat.size_pow (n := 1)
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits, hs]
  change c ∈ [_ , _, _, _, _, _, _, _, _, _, _, _] ++ _ at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_replicate] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨_, rfl⟩ <;>
    simp only [RationalCall.lhs, RationalCall.rhs] <;>
    change L _ ≤ _ ∧ L _ ≤ _ <;>
    simp only [coordinateQuery] at * <;> omega

theorem traceIterate_mem (f : RationalRegisters → RationalRun)
    (g : RationalRegisters → RationalRegisters) (h : ∀ s, (f s).1 = g s)
    (n : ℕ) (s : RationalRegisters) (c : RationalCall)
    (hc : c ∈ (traceIterate f n s).2) :
    ∃ i < n, c ∈ (f (registerIterate g i s)).2 := by
  induction n generalizing s with
  | zero => simp [traceIterate] at hc
  | succ n ih =>
    simp only [traceIterate, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ⟨0, by omega, hc⟩
    · obtain ⟨i, hi, hc⟩ := ih (f s).1 hc
      exact ⟨i + 1, by omega, by simpa only [registerIterate, h] using hc⟩

theorem coordinateProgram_operand_encoding (a β : ℚ) (n : ℕ) (c : RationalCall)
    (hc : c ∈ ((coordinateProgram n).run (coordinateRegisters a β 0 1)).2) :
    L c.lhs ≤ 2 * (L a + L β) + 76 * n + 255 ∧
      L c.rhs ≤ 2 * (L a + L β) + 76 * n + 255 := by
  obtain ⟨i, hi, hc⟩ := traceIterate_mem coordinateStepProgram.run coordinateStepProgram.exec
    coordinateStepProgram.run_result n (coordinateRegisters a β 0 1) c hc
  change c ∈ (coordinateStepProgram.run ((coordinateProgram i).exec
    (coordinateRegisters a β 0 1))).2 at hc
  rw [coordinateProgram_exec] at hc
  have h := coordinateStep_operand_encoding a β i c hc
  constructor <;> omega

theorem coordinateProgram_encoding (n : ℕ) :
    (coordinateProgram n).encoding ≤ n.size + 500 := by
  have h : coordinateStepProgram.encoding ≤ 499 := by
    have hs (j : ℕ) (hj : j ≤ 12) : j.size ≤ 4 := Nat.size_le.mpr (by omega)
    have h2 := hs 2 (by decide)
    have h3 := hs 3 (by decide)
    have h4 := hs 4 (by decide)
    have h5 := hs 5 (by decide)
    have h6 := hs 6 (by decide)
    have h7 := hs 7 (by decide)
    have h8 := hs 8 (by decide)
    have h9 := hs 9 (by decide)
    have h10 := hs 10 (by decide)
    have h11 := hs 11 (by decide)
    have h12 := hs 12 (by decide)
    simp [coordinateStepProgram, coordinatePolynomialProgram, coordinateClearProgram,
      rationalSequence, rationalAssign, RationalProgram.encoding,
      RationalOperand.encoding, rationalEncodingLength, numeratorBits, denominatorBits]
    omega
  change 1 + n.size + coordinateStepProgram.encoding ≤ n.size + 500
  omega

end IdentityTesting.RationalComputation
