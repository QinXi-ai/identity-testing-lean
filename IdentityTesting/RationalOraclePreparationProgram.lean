import IdentityTesting.RationalOraclePreparationExpressions
import IdentityTesting.RationalExpressionBounds

/-! Executed oracle parameter preparation from the original input registers.
The program depends on the dimension and selected field, not the rational data. -/
namespace IdentityTesting.RationalComputation

theorem RationalExpr.sum_inputs_le (es : List RationalExpr) (B : ℕ)
    (h : ∀ e ∈ es, e.inputs ≤ B) : (RationalExpr.sum es).inputs ≤ B := by
  induction es with
  | nil => simp [sum, literal, inputs, RationalOperand.slots]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun p hp => h p (by simp [hp]))
    change max e.inputs (RationalExpr.sum es).inputs ≤ B
    exact max_le he ht

theorem OraclePreparationField.inputs_le (f : OraclePreparationField) (k : ℕ) :
    (f.expression (k + 1)).inputs ≤ k + 3 := by
  have hs : (oracleSumExpr (k + 1)).inputs ≤ k + 3 := by
    apply RationalExpr.sum_inputs_le
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simp only [RationalExpr.reg, RationalExpr.inputs, RationalOperand.slots]
    have := i.isLt; omega
  have hh : (oracleInverseSumExpr (k + 1)).inputs ≤ k + 3 := by
    apply RationalExpr.sum_inputs_le
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simp only [RationalExpr.div, RationalExpr.literal, RationalExpr.reg,
      RationalExpr.inputs, RationalOperand.slots]
    have := i.isLt; omega
  have hk : (oracleDimensionExpr (k + 1)).inputs ≤ k + 3 := by
    apply RationalExpr.sum_inputs_le
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simp [RationalExpr.literal, RationalExpr.inputs, RationalOperand.slots]
  cases f <;> simp only [expression, oracleLowerExpr, oracleUpperExpr, oraclePoleExpr,
    oracleToleranceExpr, oracleMarginExpr, oracleCoefficientExpr, oracleInnerRatioExpr,
    oracleOuterRatioExpr, RationalExpr.add, RationalExpr.sub, RationalExpr.mul,
    RationalExpr.div, RationalExpr.square, RationalExpr.reg, RationalExpr.literal,
    RationalExpr.inputs, RationalOperand.slots] <;> omega

def OraclePreparationField.program (f : OraclePreparationField) (k : ℕ) : RationalProgram :=
  (f.expression (k + 1)).compile (k + 3)

def OraclePreparationField.input {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) : RationalRegisters :=
  oraclePreparationInput a t σ (List.replicate (f.expression (k + 1)).work 0)

theorem OraclePreparationField.input_length {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (f.input a t σ).length = k + 3 + (f.expression (k + 1)).work := by
  simp [input, oraclePreparationInput]; omega

theorem OraclePreparationField.program_result {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (RationalOperand.reg (k + 3)).read (((f.program k).run (f.input a t σ)).1) =
      f.value a t σ := by
  rw [RationalProgram.run_result]
  have h := (f.expression (k + 1)).compile_correct (k + 3) (f.input a t σ)
    (f.inputs_le k) (by rw [f.input_length])
  exact h.1.trans (f.expression_eval a t σ _)

theorem OraclePreparationField.expression_run_result {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (scratch : RationalRegisters) (d : ℕ)
    (hd : k + 3 ≤ d)
    (hw : d + (f.expression (k + 1)).work ≤ (oraclePreparationInput a t σ scratch).length) :
    (RationalOperand.reg d).read
      (((f.expression (k + 1)).compile d).run (oraclePreparationInput a t σ scratch)).1 = f.value a t σ ∧
    ∀ i < d, (RationalOperand.reg i).read
      (((f.expression (k + 1)).compile d).run (oraclePreparationInput a t σ scratch)).1 =
      (RationalOperand.reg i).read (oraclePreparationInput a t σ scratch) := by
  simp only [RationalProgram.run_result]
  have h := (f.expression (k + 1)).compile_correct d (oraclePreparationInput a t σ scratch)
    ((f.inputs_le k).trans hd) hw
  exact ⟨h.1.trans (f.expression_eval a t σ scratch), h.2⟩

theorem oraclePreparation_inner_precision {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (Nat.ceil ((RationalOperand.reg (k + 3)).read
      (((OraclePreparationField.innerRatio.program k).run
        (OraclePreparationField.innerRatio.input a t σ)).1))).size = allocationInnerPrecision a t σ := by
  rw [OraclePreparationField.program_result]
  rfl

theorem oraclePreparation_outer_fuel {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (Nat.ceil ((RationalOperand.reg (k + 3)).read
      (((OraclePreparationField.outerRatio.program k).run
        (OraclePreparationField.outerRatio.input a t σ)).1))).size = allocationOuterFuel a t σ := by
  rw [OraclePreparationField.program_result]
  rfl

theorem OraclePreparationField.program_calls {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (((f.program k).run (f.input a t σ)).2).length ≤ 2 * (f.expression (k + 1)).weight := by
  exact ((f.program k).run_length _).trans ((f.expression (k + 1)).compile_calls (k + 3))

theorem OraclePreparationField.program_allocated {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) : (f.program k).slots ≤ (f.input a t σ).length := by
  apply ((f.expression (k + 1)).compile_slots (k + 3)).trans
  rw [f.input_length]
  apply max_le
  · have := f.inputs_le k; omega
  · rfl

end IdentityTesting.RationalComputation
