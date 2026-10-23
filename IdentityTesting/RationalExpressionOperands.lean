import IdentityTesting.RationalExpressionCompiler

/-! Every executed compiler operand is a value of an actual subexpression,
or the fixed zero operand of a copy. -/
namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def RationalExpr.ValuesBound (s : RationalRegisters) (B : ℕ) : RationalExpr → Prop
  | .operand o => L (o.read s) ≤ B
  | .binary op a b => L (op.eval (a.eval s) (b.eval s)) ≤ B ∧ a.ValuesBound s B ∧ b.ValuesBound s B
  | .minimum a b => L (min (a.eval s) (b.eval s)) ≤ B ∧ a.ValuesBound s B ∧ b.ValuesBound s B

theorem RationalExpr.ValuesBound.eval_le {e : RationalExpr} {s : RationalRegisters} {B : ℕ}
    (h : e.ValuesBound s B) : L (e.eval s) ≤ B := by
  cases e <;> simp only [ValuesBound, RationalExpr.eval] at *
  · exact h
  · exact h.1
  · exact h.1

theorem RationalExpr.ValuesBound.mono {e : RationalExpr} {s : RationalRegisters} {B C : ℕ}
    (h : e.ValuesBound s B) (hBC : B ≤ C) : e.ValuesBound s C := by
  induction e with
  | operand o => exact h.trans hBC
  | binary op a b ha hb => exact ⟨h.1.trans hBC, ha h.2.1, hb h.2.2⟩
  | minimum a b ha hb => exact ⟨h.1.trans hBC, ha h.2.1, hb h.2.2⟩

theorem RationalExpr.valuesBound_congr (e : RationalExpr) (s t : RationalRegisters) (B : ℕ)
    (h : ∀ i < e.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t) :
    e.ValuesBound s B ↔ e.ValuesBound t B := by
  induction e with
  | operand o => simp only [ValuesBound, o.read_congr s t h]
  | binary op a b ha hb =>
    have hia : ∀ i < a.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t :=
      fun i hi => h i (by simp only [inputs]; omega)
    have hib : ∀ i < b.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t :=
      fun i hi => h i (by simp only [inputs]; omega)
    simp only [ValuesBound, a.eval_congr s t hia, b.eval_congr s t hib, ha hia, hb hib]
  | minimum a b ha hb =>
    have hia : ∀ i < a.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t :=
      fun i hi => h i (by simp only [inputs]; omega)
    have hib : ∀ i < b.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t :=
      fun i hi => h i (by simp only [inputs]; omega)
    simp only [ValuesBound, a.eval_congr s t hia, b.eval_congr s t hib, ha hia, hb hib]

theorem RationalExpr.compile_operands (e : RationalExpr) (d : ℕ) (s : RationalRegisters)
    (B : ℕ) (hB : 2 ≤ B) (hv : e.ValuesBound s B)
    (hi : e.inputs ≤ d) (hw : d + e.work ≤ s.length)
    (c : RationalCall) (hc : c ∈ ((e.compile d).run s).2) :
    L c.lhs ≤ B ∧ L c.rhs ≤ B := by
  have hz : L 0 = 2 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  induction e generalizing d s c with
  | operand o =>
    simp only [compile, RationalProgram.run, List.mem_singleton] at hc
    subst c
    exact ⟨hv, by simpa only [RationalInstruction.call, RationalOperand.read, hz] using hB⟩
  | binary op a b ha hb =>
    have hia : a.inputs ≤ d := by simp only [inputs] at hi; omega
    have hib : b.inputs ≤ d := by simp only [inputs] at hi; omega
    have hwa : d + a.work ≤ s.length := by simp only [work] at hw; omega
    have hwb : d + 1 + b.work ≤ ((a.compile d).exec s).length := by
      rw [RationalProgram.exec_length]; simp only [work] at hw; omega
    obtain ⟨har, haf⟩ := a.compile_correct d s hia hwa
    obtain ⟨hbr, hbf⟩ := b.compile_correct (d + 1) ((a.compile d).exec s) (by omega) hwb
    have hbe := b.eval_congr ((a.compile d).exec s) s (fun i hii => haf i (by omega))
    rw [hbe] at hbr
    have had := hbf d (by omega)
    rw [har] at had
    have hvb : b.ValuesBound ((a.compile d).exec s) B :=
      (b.valuesBound_congr _ _ B (fun i hii => haf i (by omega))).mpr hv.2.2
    simp only [compile, RationalProgram.run, RationalProgram.run_result, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | rfl
    · exact ha d s hv.2.1 hia hwa c hc
    · exact hb (d + 1) _ hvb (by omega) hwb c hc
    · simp only [RationalInstruction.call, had, hbr]
      exact ⟨hv.2.1.eval_le, hv.2.2.eval_le⟩
  | minimum a b ha hb =>
    have hia : a.inputs ≤ d := by simp only [inputs] at hi; omega
    have hib : b.inputs ≤ d := by simp only [inputs] at hi; omega
    have hwa : d + a.work ≤ s.length := by simp only [work] at hw; omega
    have hwb : d + 1 + b.work ≤ ((a.compile d).exec s).length := by
      rw [RationalProgram.exec_length]; simp only [work] at hw; omega
    obtain ⟨har, haf⟩ := a.compile_correct d s hia hwa
    obtain ⟨hbr, hbf⟩ := b.compile_correct (d + 1) ((a.compile d).exec s) (by omega) hwb
    have hbe := b.eval_congr ((a.compile d).exec s) s (fun i hii => haf i (by omega))
    rw [hbe] at hbr
    have had := hbf d (by omega)
    rw [har] at had
    have hvb : b.ValuesBound ((a.compile d).exec s) B :=
      (b.valuesBound_congr _ _ B (fun i hii => haf i (by omega))).mpr hv.2.2
    simp only [compile, RationalProgram.run, RationalProgram.run_result,
      RationalInstruction.call, RationalCall.result, RationalOp.eval, had, hbr,
      List.mem_append, List.mem_cons] at hc
    rcases hc with hc | hc | rfl | hc
    · exact ha d s hv.2.1 hia hwa c hc
    · exact hb (d + 1) _ hvb (by omega) hwb c hc
    · exact ⟨hv.2.1.eval_le, hv.2.2.eval_le⟩
    · by_cases hab : a.eval s ≤ b.eval s
      · simp [hab] at hc
      · simp only [hab, if_false, zero_ne_one, List.mem_singleton] at hc
        subst c
        exact ⟨hv.2.2.eval_le, by simpa only [RationalOperand.read, hz] using hB⟩

end IdentityTesting.RationalComputation
