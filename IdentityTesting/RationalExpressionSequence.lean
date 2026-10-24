import IdentityTesting.RationalDynamicControl
import IdentityTesting.RationalExpressionCompiler

/-! A sequence of input-reading expressions writes consecutive output registers.
Later expressions reuse the scratch region while preserving earlier outputs.
Ceil-size is an explicit control primitive and remains visible in the trace. -/
namespace IdentityTesting.RationalComputation

structure RationalPreparedExpr where
  expression : RationalExpr
  ceilSize : Bool := false
  deriving Repr

def RationalPreparedExpr.eval (e : RationalPreparedExpr) (s : RationalRegisters) : ℚ :=
  if e.ceilSize then ((Nat.ceil (e.expression.eval s)).size : ℚ) else e.expression.eval s

def RationalPreparedExpr.compile (e : RationalPreparedExpr) (d : ℕ) : RationalControlProgram :=
  .seq (.basic (e.expression.compile d))
    (if e.ceilSize then .ceilSize d (.reg d) else .basic .skip)

theorem RationalPreparedExpr.compile_correct (e : RationalPreparedExpr) (d : ℕ)
    (s : RationalRegisters) (hi : e.expression.inputs ≤ d)
    (hw : d + e.expression.work ≤ s.length) :
    (RationalOperand.reg d).read ((e.compile d).exec s) = e.eval s ∧
      ∀ i < d, (RationalOperand.reg i).read ((e.compile d).exec s) = (RationalOperand.reg i).read s := by
  obtain ⟨hr, hf⟩ := e.expression.compile_correct d s hi hw
  have hd : d < ((e.expression.compile d).exec s).length := by
    rw [RationalProgram.exec_length]
    have := e.expression.work_pos
    omega
  cases hc : e.ceilSize with
  | false => simpa only [compile, hc, Bool.false_eq_true, if_false,
      RationalControlProgram.exec, RationalProgram.exec, eval] using And.intro hr hf
  | true =>
    simp only [compile, hc, if_true, RationalControlProgram.exec, eval]
    refine ⟨?_, ?_⟩
    · rw [rationalRegister_read_set _ _ _ hd, hr]
    · intro i hii
      rw [rationalRegister_read_set_ne _ d i _ (by omega)]
      exact hf i hii

def rationalPrepareExpressions : List RationalPreparedExpr → ℕ → RationalControlProgram
  | [], _ => .basic .skip
  | e :: es, d => .seq (e.compile d) (rationalPrepareExpressions es (d + 1))

def rationalPreparationWork : List RationalPreparedExpr → ℕ
  | [] => 0
  | e :: es => e.expression.work + rationalPreparationWork es

theorem rationalPreparationWork_length (es : List RationalPreparedExpr) :
    es.length ≤ rationalPreparationWork es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have := e.expression.work_pos
    simp only [List.length_cons, rationalPreparationWork]
    omega

theorem rationalPrepareExpressions_correct (es : List RationalPreparedExpr)
    (d b : ℕ) (s reference : RationalRegisters) (hb : b ≤ d)
    (hi : ∀ e ∈ es, e.expression.inputs ≤ b)
    (href : ∀ i < b, (RationalOperand.reg i).read s = (RationalOperand.reg i).read reference)
    (hw : d + rationalPreparationWork es ≤ s.length) :
    (∀ i < d, (RationalOperand.reg i).read ((rationalPrepareExpressions es d).exec s) =
      (RationalOperand.reg i).read s) ∧
    (∀ j (hj : j < es.length),
      (RationalOperand.reg (d + j)).read ((rationalPrepareExpressions es d).exec s) =
        (es[j]).eval reference) := by
  induction es generalizing d s with
  | nil => exact ⟨fun _ _ => rfl, fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | cons e es ih =>
    have he := hi e (by simp)
    have ht (f : RationalPreparedExpr) (hf : f ∈ es) : f.expression.inputs ≤ b :=
      hi f (by simp [hf])
    have hew := e.expression.work_pos
    have her := e.compile_correct d s (he.trans hb) (by simp only [rationalPreparationWork] at hw; omega)
    have heval : e.eval s = e.eval reference := by
      have h := e.expression.eval_congr s reference (fun i hii => href i (by omega))
      simp only [RationalPreparedExpr.eval, h]
    have hit := ih (d + 1) ((e.compile d).exec s)
      (by omega) ht
      (fun i hii => (her.2 i (by omega)).trans (href i hii)) (by
        rw [RationalControlProgram.exec_length]
        simp only [rationalPreparationWork] at hw
        omega)
    refine ⟨?_, ?_⟩
    · intro i hii
      exact (hit.1 i (by omega)).trans (her.2 i hii)
    · intro j hj
      cases j with
      | zero =>
        simpa only [Nat.add_zero, List.getElem_cons_zero, rationalPrepareExpressions,
          RationalControlProgram.exec] using (hit.1 d (by omega)).trans (her.1.trans heval)
      | succ j =>
        simpa only [Nat.add_succ, Nat.succ_add, Nat.add_zero,
          List.getElem_cons_succ, rationalPrepareExpressions, RationalControlProgram.exec]
          using hit.2 j (by simpa using hj)
end IdentityTesting.RationalComputation
