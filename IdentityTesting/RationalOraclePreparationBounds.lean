import IdentityTesting.RationalOraclePreparationProgram

/-! Polynomial resource bounds for the actual input-reading preparation code. -/
namespace IdentityTesting.RationalComputation

theorem RationalExpr.literal_weight_le (n : ℕ) :
    (RationalExpr.literal (n : ℚ)).weight ≤ n + 4 := by
  have h := rational_natCast_encoding_le n
  simp only [literal, weight, RationalOperand.slots, RationalOperand.encoding]
  omega

theorem RationalExpr.reg_weight_le (i : ℕ) : (RationalExpr.reg i).weight ≤ 2 * i + 3 := by
  have h : i.size ≤ i := Nat.size_le.mpr i.lt_two_pow_self
  simp only [reg, weight, RationalOperand.slots, RationalOperand.encoding]
  omega

theorem RationalExpr.sum_weight_le (es : List RationalExpr) (B : ℕ)
    (h : ∀ e ∈ es, e.weight ≤ B) : (RationalExpr.sum es).weight ≤ es.length * (B + 1) + 4 := by
  induction es with
  | nil =>
    simpa only [sum, List.foldr_nil, List.length_nil, zero_mul, zero_add, Nat.cast_zero] using
      RationalExpr.literal_weight_le 0
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    change e.weight + (RationalExpr.sum es).weight + 1 ≤ (es.length + 1) * (B + 1) + 4
    nlinarith

theorem oraclePreparationSum_weights (k : ℕ) :
    (oracleSumExpr k).weight ≤ 20 * (k + 3) ^ 2 ∧
    (oracleInverseSumExpr k).weight ≤ 20 * (k + 3) ^ 2 ∧
    (oracleDimensionExpr k).weight ≤ 20 * (k + 3) ^ 2 := by
  have hs := RationalExpr.sum_weight_le
    (List.ofFn (fun i : Fin k => RationalExpr.reg (2 + i))) (2 * k + 7) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      have h := RationalExpr.reg_weight_le (2 + i)
      have hi := i.isLt
      omega)
  have hh := RationalExpr.sum_weight_le
    (List.ofFn (fun i : Fin k => (RationalExpr.literal 1).div (.reg (2 + i)))) (2 * k + 13) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      have h := RationalExpr.reg_weight_le (2 + i)
      have h1 := RationalExpr.literal_weight_le 1
      have hi := i.isLt
      simp only [RationalExpr.div, RationalExpr.weight]
      norm_num only [Nat.cast_one] at h1
      omega)
  have hk := RationalExpr.sum_weight_le
    (List.ofFn (fun _ : Fin k => RationalExpr.literal 1)) 5 (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      exact RationalExpr.literal_weight_le 1)
  simp only [List.length_ofFn] at hs hh hk
  change _ ∧ _ ∧ _
  unfold oracleSumExpr oracleInverseSumExpr oracleDimensionExpr
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem OraclePreparationField.weight_le (f : OraclePreparationField) (k : ℕ) :
    (f.expression (k + 1)).weight ≤ 1000000 * (k + 4) ^ 2 := by
  obtain ⟨hs, hh, hk⟩ := oraclePreparationSum_weights (k + 1)
  have h0 := RationalExpr.reg_weight_le 0
  have h1 := RationalExpr.reg_weight_le 1
  have h2 := RationalExpr.reg_weight_le 2
  have c1 := RationalExpr.literal_weight_le 1
  have c2 := RationalExpr.literal_weight_le 2
  have c4 := RationalExpr.literal_weight_le 4
  have c100 := RationalExpr.literal_weight_le 100
  have c128 := RationalExpr.literal_weight_le 128
  norm_num only [Nat.cast_ofNat] at c1 c2 c4 c100 c128
  have hW : 1 ≤ (k + 4) ^ 2 := by
    have : 0 < (k + 4) ^ 2 := by positivity
    omega
  norm_num only [Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] at hs hh hk h0 h1 h2
  cases f <;> simp only [expression, oracleLowerExpr, oracleUpperExpr, oraclePoleExpr,
    oracleToleranceExpr, oracleMarginExpr, oracleCoefficientExpr, oracleInnerRatioExpr,
    oracleOuterRatioExpr, RationalExpr.add, RationalExpr.sub, RationalExpr.mul,
    RationalExpr.div, RationalExpr.square, RationalExpr.weight] <;> omega

theorem OraclePreparationField.program_calls_polynomial {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (((f.program k).run (f.input a t σ)).2).length ≤ 2000000 * (k + 4) ^ 2 := by
  have h := f.program_calls a t σ
  have hw := f.weight_le k
  omega

theorem OraclePreparationField.program_memory_polynomial {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (f.input a t σ).length ≤ k + 3 + 1000000 * (k + 4) ^ 2 := by
  rw [f.input_length]
  have hw := (f.expression (k + 1)).work_le_weight
  have hp := f.weight_le k
  omega

theorem OraclePreparationField.program_encoding_polynomial (f : OraclePreparationField) (k : ℕ) :
    (f.program k).encoding ≤
      100 * (k + 4 + 1000000 * (k + 4) ^ 2) * (1000000 * (k + 4) ^ 2) := by
  have h := (f.expression (k + 1)).compile_encoding (k + 3)
  have hw := f.weight_le k
  apply h.trans
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul_left
    omega
  · exact hw

end IdentityTesting.RationalComputation
