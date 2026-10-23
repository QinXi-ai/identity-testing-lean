import IdentityTesting.RationalExpressionValueBounds
import IdentityTesting.RationalOraclePreparationProgram

/-! Polynomial encoding bounds for every operand of actual initialization. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def oraclePreparationBase {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℕ :=
  100 * (k + 4) * (allocationOracleInputLength a t σ + 1) + 100

theorem OraclePreparationField.values_bound {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (scratch : RationalRegisters) :
    (f.expression (k + 1)).ValuesBound (oraclePreparationInput a t σ scratch)
      (10000000 * oraclePreparationBase a t σ) := by
  let S := allocationOracleInputLength a t σ
  let U := oraclePreparationBase a t σ
  let s := oraclePreparationInput a t σ scratch
  have hU : 130 ≤ U := by dsimp [U, oraclePreparationBase]; nlinarith
  have hS : 1 ≤ S := by
    have htpos : 1 ≤ L t := by unfold rationalEncodingLength; omega
    dsimp [S, allocationOracleInputLength]
    omega
  have htL : L t ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have hσL : L σ ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have haL (i : Fin (k + 1)) : L (a i) ≤ S := by
    have h := rational_entry_encoding_le a i
    dsimp [S, allocationOracleInputLength]; omega
  have hSU : S ≤ U := by dsimp [U, oraclePreparationBase, S]; nlinarith
  have hc (n : ℕ) (hn : n ≤ 128) : (RationalExpr.literal (n : ℚ)).ValuesBound s U := by
    have h := rational_natCast_encoding_le n
    change L (n : ℚ) ≤ U
    omega
  have ht : (RationalExpr.reg 0).ValuesBound s U := by
    change L ((RationalOperand.reg 0).read s) ≤ U
    rw [oraclePreparationInput_read0]
    exact htL.trans hSU
  have hσ : (RationalExpr.reg 1).ValuesBound s U := by
    change L ((RationalOperand.reg 1).read s) ≤ U
    rw [oraclePreparationInput_read1]
    exact hσL.trans hSU
  have ha0 : (RationalExpr.reg 2).ValuesBound s U := by
    have h := oraclePreparationInput_readAtom a t σ scratch 0
    norm_num only [Fin.val_zero, add_zero] at h
    change L ((RationalOperand.reg 2).read s) ≤ U
    rw [h]
    exact (haL 0).trans hSU
  have hsum : (oracleSumExpr (k + 1)).ValuesBound s U := by
    have h := RationalExpr.sum_valuesBound
      (List.ofFn (fun i : Fin (k + 1) => RationalExpr.reg (2 + i))) s S (by
        intro e he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
        change L ((RationalOperand.reg (2 + i)).read s) ≤ S
        rw [oraclePreparationInput_readAtom]
        exact haL i)
    apply h.mono
    simp only [List.length_ofFn]
    dsimp [U, oraclePreparationBase, S] at *
    nlinarith
  have hinv : (oracleInverseSumExpr (k + 1)).ValuesBound s U := by
    have ho : L 1 = 3 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
    have h := RationalExpr.sum_valuesBound
      (List.ofFn (fun i : Fin (k + 1) => (RationalExpr.literal 1).div (.reg (2 + i)))) s (S + 5) (by
        intro e he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
        have hi := haL i
        have hd := rational_div_encoding_le 1 (a i)
        change L (1 / (RationalOperand.reg (2 + i)).read s) ≤ S + 5 ∧
          L 1 ≤ S + 5 ∧ L ((RationalOperand.reg (2 + i)).read s) ≤ S + 5
        rw [oraclePreparationInput_readAtom]
        exact ⟨by omega, by omega, by omega⟩)
    apply h.mono
    simp only [List.length_ofFn]
    dsimp [U, oraclePreparationBase, S] at *
    nlinarith
  have hdim : (oracleDimensionExpr (k + 1)).ValuesBound s U := by
    have h := RationalExpr.sum_valuesBound
      (List.ofFn (fun _ : Fin (k + 1) => RationalExpr.literal 1)) s 3 (by
        intro e he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
        norm_num [RationalExpr.literal, RationalExpr.ValuesBound, RationalOperand.read,
          rationalEncodingLength, numeratorBits, denominatorBits])
    apply h.mono
    simp only [List.length_ofFn]
    dsimp [U, oraclePreparationBase, S] at *
    nlinarith
  have h1 := hc 1 (by decide)
  have h2 := hc 2 (by decide)
  have h4 := hc 4 (by decide)
  have h100 := hc 100 (by decide)
  have h128 := hc 128 (by decide)
  norm_num only [Nat.cast_ofNat] at h1 h2 h4 h100 h128
  have hLower := h1.div (ht.square.mul hsum)
  have hUpper := (h1.add (ht.square.mul ha0.square)).square.div
    (ht.square.square.mul (ha0.square.mul ha0))
  have hPole := (h1.div h2).minimum ((h1.div hinv).div (h128.mul hUpper))
  have hTolerance := hσ.div (h100.mul hsum)
  have hMargin := hσ.div h100
  have hCoefficient := (((h4.mul hdim).mul ht.square).mul hsum.square).div hPole.square
  have hInner := h1.div (hTolerance.minimum (hTolerance.div hCoefficient))
  have hOuter := (hUpper.sub hLower).div (hTolerance.mul hLower)
  change (f.expression (k + 1)).ValuesBound s (10000000 * U)
  cases f with
  | lower => exact hLower.mono (by omega)
  | upper => exact hUpper.mono (by omega)
  | pole => exact hPole.mono (by omega)
  | tolerance => exact hTolerance.mono (by omega)
  | margin => exact hMargin.mono (by omega)
  | innerRatio => exact hInner.mono (by omega)
  | outerRatio => exact hOuter.mono (by omega)

theorem OraclePreparationField.program_operands {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (c : RationalCall)
    (hc : c ∈ ((f.program k).run (f.input a t σ)).2) :
    L c.lhs ≤ 10000000 * oraclePreparationBase a t σ ∧
      L c.rhs ≤ 10000000 * oraclePreparationBase a t σ := by
  apply (f.expression (k + 1)).compile_operands (k + 3) (f.input a t σ) _
  · unfold oraclePreparationBase; omega
  · exact f.values_bound a t σ _
  · exact f.inputs_le k
  · rw [f.input_length]
  · exact hc

end IdentityTesting.RationalComputation
