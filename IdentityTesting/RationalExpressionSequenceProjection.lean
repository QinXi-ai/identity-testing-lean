import IdentityTesting.RationalExpressionSequence

/-! The initialized consecutive register block is exactly the list of
expression values; any later scratch registers are retained explicitly. -/
namespace IdentityTesting.RationalComputation

theorem rationalPrepareExpressions_block (es : List RationalPreparedExpr)
    (d b : ℕ) (s reference : RationalRegisters) (hb : b ≤ d)
    (hi : ∀ e ∈ es, e.expression.inputs ≤ b)
    (href : ∀ i < b, (RationalOperand.reg i).read s = (RationalOperand.reg i).read reference)
    (hw : d + rationalPreparationWork es ≤ s.length) :
    ((((rationalPrepareExpressions es d).exec s).drop d).take es.length) =
      es.map (fun e => e.eval reference) := by
  have h := rationalPrepareExpressions_correct es d b s reference hb hi href hw
  have hlen : d + es.length ≤ ((rationalPrepareExpressions es d).exec s).length := by
    rw [RationalControlProgram.exec_length]
    have := rationalPreparationWork_length es
    omega
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map]
    omega
  · intro i hil hir
    have hie : i < es.length := by simpa only [List.length_map] using hir
    have hid : d + i < ((rationalPrepareExpressions es d).exec s).length := by omega
    have hv := h.2 i hie
    simp only [RationalOperand.read, List.getElem?_eq_getElem hid, Option.getD_some] at hv
    simpa only [List.getElem_take, List.getElem_drop, List.getElem_map] using hv

theorem rationalPrepareExpressions_suffix (es : List RationalPreparedExpr)
    (d b : ℕ) (s reference : RationalRegisters) (hb : b ≤ d)
    (hi : ∀ e ∈ es, e.expression.inputs ≤ b)
    (href : ∀ i < b, (RationalOperand.reg i).read s = (RationalOperand.reg i).read reference)
    (hw : d + rationalPreparationWork es ≤ s.length) :
    ((rationalPrepareExpressions es d).exec s).drop d =
      es.map (fun e => e.eval reference) ++
        (((rationalPrepareExpressions es d).exec s).drop d).drop es.length := by
  rw [← rationalPrepareExpressions_block es d b s reference hb hi href hw]
  exact (List.take_append_drop _ _).symm

end IdentityTesting.RationalComputation
