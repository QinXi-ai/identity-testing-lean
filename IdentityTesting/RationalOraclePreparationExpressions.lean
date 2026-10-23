import IdentityTesting.RationalExpressionCompiler
import IdentityTesting.RationalOracleParameterEncoding

/-! Fixed input-reading expressions for oracle initialization. The two final
expressions are the actual rational inputs to the binary ceil-size primitive. -/
namespace IdentityTesting.RationalComputation
open scoped BigOperators

def RationalExpr.literal (q : ℚ) : RationalExpr := .operand (.literal q)
def RationalExpr.reg (i : ℕ) : RationalExpr := .operand (.reg i)
def RationalExpr.add (a b : RationalExpr) : RationalExpr := .binary .add a b
def RationalExpr.sub (a b : RationalExpr) : RationalExpr := .binary .sub a b
def RationalExpr.mul (a b : RationalExpr) : RationalExpr := .binary .mul a b
def RationalExpr.div (a b : RationalExpr) : RationalExpr := .binary .div a b
def RationalExpr.square (a : RationalExpr) : RationalExpr := a.mul a
def RationalExpr.sum (es : List RationalExpr) : RationalExpr :=
  es.foldr RationalExpr.add (.literal 0)

private theorem literal_read (q : ℚ) (s : RationalRegisters) :
    (RationalOperand.literal q).read s = q := rfl

theorem RationalExpr.eval_sum (es : List RationalExpr) (s : RationalRegisters) :
    (RationalExpr.sum es).eval s = (es.map (RationalExpr.eval s)).sum := by
  induction es with
  | nil => simp [sum, literal, eval, RationalOperand.read]
  | cons e es ih => simpa [sum, add, eval, RationalOp.eval] using congrArg (e.eval s + ·) ih

def oraclePreparationInput {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ)
    (scratch : RationalRegisters) : RationalRegisters := [t, σ] ++ List.ofFn a ++ scratch

theorem oraclePreparationInput_read0 {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ)
    (scratch : RationalRegisters) : (RationalOperand.reg 0).read (oraclePreparationInput a t σ scratch) = t := by
  simp [oraclePreparationInput, RationalOperand.read]

theorem oraclePreparationInput_read1 {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ)
    (scratch : RationalRegisters) : (RationalOperand.reg 1).read (oraclePreparationInput a t σ scratch) = σ := by
  simp [oraclePreparationInput, RationalOperand.read]

theorem oraclePreparationInput_readAtom {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ)
    (scratch : RationalRegisters) (i : Fin k) :
    (RationalOperand.reg (2 + i)).read (oraclePreparationInput a t σ scratch) = a i := by
  simp only [oraclePreparationInput, List.cons_append, List.nil_append, RationalOperand.read,
    Nat.add_comm 2 i.val, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using i.isLt)]
  simp

def oracleSumExpr (k : ℕ) : RationalExpr :=
  .sum (List.ofFn (fun i : Fin k => RationalExpr.reg (2 + i)))
def oracleInverseSumExpr (k : ℕ) : RationalExpr :=
  .sum (List.ofFn (fun i : Fin k => (RationalExpr.literal 1).div (.reg (2 + i))))
def oracleDimensionExpr (k : ℕ) : RationalExpr :=
  .sum (List.ofFn (fun _ : Fin k => RationalExpr.literal 1))

def oracleLowerExpr (k : ℕ) : RationalExpr :=
  (RationalExpr.literal 1).div ((RationalExpr.reg 0).square.mul (oracleSumExpr k))
def oracleUpperExpr : RationalExpr :=
  ((RationalExpr.literal 1).add ((RationalExpr.reg 0).square.mul (RationalExpr.reg 2).square)).square.div
    ((RationalExpr.reg 0).square.square.mul ((RationalExpr.reg 2).square.mul (.reg 2)))
def oraclePoleExpr (k : ℕ) : RationalExpr :=
  .minimum ((RationalExpr.literal 1).div (.literal 2))
    (((RationalExpr.literal 1).div (oracleInverseSumExpr k)).div
      ((RationalExpr.literal 128).mul oracleUpperExpr))
def oracleToleranceExpr (k : ℕ) : RationalExpr :=
  (RationalExpr.reg 1).div ((RationalExpr.literal 100).mul (oracleSumExpr k))
def oracleMarginExpr : RationalExpr := (RationalExpr.reg 1).div (.literal 100)
def oracleCoefficientExpr (k : ℕ) : RationalExpr :=
  ((((RationalExpr.literal 4).mul (oracleDimensionExpr k)).mul (RationalExpr.reg 0).square).mul
    (oracleSumExpr k).square).div (oraclePoleExpr k).square
def oracleInnerRatioExpr (k : ℕ) : RationalExpr :=
  (RationalExpr.literal 1).div
    (.minimum (oracleToleranceExpr k) ((oracleToleranceExpr k).div (oracleCoefficientExpr k)))
def oracleOuterRatioExpr (k : ℕ) : RationalExpr :=
  (oracleUpperExpr.sub (oracleLowerExpr k)).div
    ((oracleToleranceExpr k).mul (oracleLowerExpr k))

theorem oracleSumExpr_eval {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ) (scratch : RationalRegisters) :
    (oracleSumExpr k).eval (oraclePreparationInput a t σ scratch) = ∑ i, a i := by
  simp only [oracleSumExpr, RationalExpr.eval_sum, List.map_ofFn, RationalExpr.reg,
    Function.comp_apply, RationalExpr.eval, oraclePreparationInput_readAtom, List.sum_ofFn]

theorem oracleInverseSumExpr_eval {k : ℕ} (a : Fin k → ℚ) (t σ : ℚ) (scratch : RationalRegisters) :
    (oracleInverseSumExpr k).eval (oraclePreparationInput a t σ scratch) = ∑ i, 1 / a i := by
  simp only [oracleInverseSumExpr, RationalExpr.eval_sum, List.map_ofFn, RationalExpr.div,
    RationalExpr.literal, RationalExpr.reg, Function.comp_apply, RationalExpr.eval, RationalOp.eval,
    oraclePreparationInput_readAtom, literal_read, List.sum_ofFn]

theorem oracleDimensionExpr_eval (k : ℕ) (s : RationalRegisters) :
    (oracleDimensionExpr k).eval s = k := by
  simp [oracleDimensionExpr, RationalExpr.eval_sum, RationalExpr.literal,
    RationalExpr.eval, RationalOperand.read, List.sum_ofFn]

inductive OraclePreparationField where
  | lower | upper | pole | tolerance | margin | innerRatio | outerRatio
  deriving Repr

def OraclePreparationField.expression (k : ℕ) : OraclePreparationField → RationalExpr
  | .lower => oracleLowerExpr k
  | .upper => oracleUpperExpr
  | .pole => oraclePoleExpr k
  | .tolerance => oracleToleranceExpr k
  | .margin => oracleMarginExpr
  | .innerRatio => oracleInnerRatioExpr k
  | .outerRatio => oracleOuterRatioExpr k

def OraclePreparationField.value {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    OraclePreparationField → ℚ
  | .lower => oracleBetaLower a t
  | .upper => oracleBetaUpper (a 0) t
  | .pole => oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
  | .tolerance => σ / (100 * ∑ i, a i)
  | .margin => σ / 100
  | .innerRatio => 1 / min (σ / (100 * ∑ i, a i))
      ((σ / (100 * ∑ i, a i)) / allocationOracleCoefficient a t)
  | .outerRatio => (oracleBetaUpper (a 0) t - oracleBetaLower a t) /
      ((σ / (100 * ∑ i, a i)) * oracleBetaLower a t)

theorem OraclePreparationField.expression_eval {k : ℕ} (f : OraclePreparationField)
    (a : Fin (k + 1) → ℚ) (t σ : ℚ) (scratch : RationalRegisters) :
    (f.expression (k + 1)).eval (oraclePreparationInput a t σ scratch) = f.value a t σ := by
  have ha0 := oraclePreparationInput_readAtom a t σ scratch 0
  norm_num only [Fin.val_zero, add_zero] at ha0
  cases f <;>
    simp only [expression, value, oracleLowerExpr, oracleUpperExpr, oraclePoleExpr,
      oracleToleranceExpr, oracleMarginExpr, oracleCoefficientExpr, oracleInnerRatioExpr,
      oracleOuterRatioExpr, RationalExpr.add, RationalExpr.sub, RationalExpr.mul,
      RationalExpr.div, RationalExpr.square, RationalExpr.reg, RationalExpr.literal,
      RationalExpr.eval, RationalOp.eval, oracleSumExpr_eval, oracleInverseSumExpr_eval,
      oracleDimensionExpr_eval, oraclePreparationInput_read0, oraclePreparationInput_read1,
      ha0, oracleBetaLower, oracleBetaUpper, oraclePoleGap,
      oracleAtomLower, allocationOracleCoefficient]
  all_goals simp only [RationalOperand.read] at *
  all_goals simp only [oraclePreparationInput, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.getElem?_append_left (show 0 < (List.ofFn a).length by simp),
    List.getElem?_ofFn, Nat.cast_add, Nat.cast_one] at *
  all_goals simp only [mul_assoc, pow_succ, pow_zero, one_mul]

end IdentityTesting.RationalComputation
