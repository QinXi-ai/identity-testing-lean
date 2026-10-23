import IdentityTesting.RationalInstructionTraceBounds

/-! Arithmetic expressions read input registers and compile to actual rational
instructions using fresh registers. Expression values are never inserted into
the instruction syntax. -/
namespace IdentityTesting.RationalComputation

inductive RationalExpr where
  | operand (o : RationalOperand)
  | binary (op : RationalOp) (a b : RationalExpr)
  | minimum (a b : RationalExpr)
  deriving Repr

def RationalExpr.eval (s : RationalRegisters) : RationalExpr → ℚ
  | .operand o => o.read s
  | .binary op a b => op.eval (a.eval s) (b.eval s)
  | .minimum a b => min (a.eval s) (b.eval s)

def RationalExpr.inputs : RationalExpr → ℕ
  | .operand o => o.slots
  | .binary _ a b | .minimum a b => max a.inputs b.inputs

def RationalExpr.work : RationalExpr → ℕ
  | .operand _ => 1
  | .binary _ a b | .minimum a b => max a.work (1 + b.work)

def RationalExpr.compile (d : ℕ) : RationalExpr → RationalProgram
  | .operand o => .instr ⟨d, .copy, o, .literal 0⟩
  | .binary op a b => .seq (a.compile d)
    (.seq (b.compile (d + 1)) (.instr ⟨d, op, .reg d, .reg (d + 1)⟩))
  | .minimum a b => .seq (a.compile d)
    (.seq (b.compile (d + 1))
      (.branchLe (.reg d) (.reg (d + 1)) .skip (.instr ⟨d, .copy, .reg (d + 1), .literal 0⟩)))

theorem RationalExpr.work_pos (e : RationalExpr) : 0 < e.work := by
  cases e <;> simp only [work] <;> omega

theorem RationalOperand.read_congr (o : RationalOperand) (s t : RationalRegisters)
    (h : ∀ i < o.slots, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t) :
    o.read s = o.read t := by
  cases o with
  | literal q => rfl
  | reg i => exact h i (by simp [slots])

theorem RationalExpr.eval_congr (e : RationalExpr) (s t : RationalRegisters)
    (h : ∀ i < e.inputs, (RationalOperand.reg i).read s = (RationalOperand.reg i).read t) :
    e.eval s = e.eval t := by
  induction e with
  | operand o => exact o.read_congr s t h
  | binary op a b ha hb =>
    simp only [eval]
    rw [ha (fun i hi => h i (by simp only [inputs]; omega)),
      hb (fun i hi => h i (by simp only [inputs]; omega))]
  | minimum a b ha hb =>
    simp only [eval]
    rw [ha (fun i hi => h i (by simp only [inputs]; omega)),
      hb (fun i hi => h i (by simp only [inputs]; omega))]

theorem rationalRegister_read_set (s : RationalRegisters) (d : ℕ) (v : ℚ)
    (hd : d < s.length) : (RationalOperand.reg d).read (s.set d v) = v := by
  simp only [RationalOperand.read, List.getElem?_set_self hd, Option.getD_some]

theorem rationalRegister_read_set_ne (s : RationalRegisters) (d i : ℕ) (v : ℚ)
    (hi : d ≠ i) : (RationalOperand.reg i).read (s.set d v) = (RationalOperand.reg i).read s := by
  simp only [RationalOperand.read, List.getElem?_set_ne hi]

theorem RationalExpr.compile_correct (e : RationalExpr) (d : ℕ) (s : RationalRegisters)
    (hi : e.inputs ≤ d) (hw : d + e.work ≤ s.length) :
    (RationalOperand.reg d).read ((e.compile d).exec s) = e.eval s ∧
      ∀ i < d, (RationalOperand.reg i).read ((e.compile d).exec s) =
        (RationalOperand.reg i).read s := by
  induction e generalizing d s with
  | operand o =>
    have hd : d < s.length := by simp only [work] at hw; omega
    simp only [compile, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalCall.result, RationalOp.eval, eval]
    refine ⟨rationalRegister_read_set s d (o.read s) hd, ?_⟩
    intro i hdi
    exact rationalRegister_read_set_ne s d i (o.read s) (by omega)
  | binary op a b ha hb =>
    have hia : a.inputs ≤ d := by simp only [inputs] at hi; omega
    have hib : b.inputs ≤ d := by simp only [inputs] at hi; omega
    have hwa : d + a.work ≤ s.length := by simp only [work] at hw; omega
    have hwb : d + 1 + b.work ≤ ((a.compile d).exec s).length := by
      rw [RationalProgram.exec_length]; simp only [work] at hw; omega
    obtain ⟨har, haf⟩ := ha d s hia hwa
    obtain ⟨hbr, hbf⟩ := hb (d + 1) ((a.compile d).exec s) (by omega) hwb
    have hbe : b.eval ((a.compile d).exec s) = b.eval s :=
      b.eval_congr _ _ (fun i hii => haf i (by omega))
    rw [hbe] at hbr
    have had := hbf d (by omega)
    rw [har] at had
    have hlen : d < ((b.compile (d + 1)).exec ((a.compile d).exec s)).length := by
      simp only [RationalProgram.exec_length]
      have := a.work_pos
      omega
    simp only [compile, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalCall.result, had, hbr, eval]
    refine ⟨rationalRegister_read_set _ d _ hlen, ?_⟩
    intro i hii
    rw [rationalRegister_read_set_ne _ d i _ (by omega), hbf i (by omega), haf i hii]
  | minimum a b ha hb =>
    have hia : a.inputs ≤ d := by simp only [inputs] at hi; omega
    have hib : b.inputs ≤ d := by simp only [inputs] at hi; omega
    have hwa : d + a.work ≤ s.length := by simp only [work] at hw; omega
    have hwb : d + 1 + b.work ≤ ((a.compile d).exec s).length := by
      rw [RationalProgram.exec_length]; simp only [work] at hw; omega
    obtain ⟨har, haf⟩ := ha d s hia hwa
    obtain ⟨hbr, hbf⟩ := hb (d + 1) ((a.compile d).exec s) (by omega) hwb
    have hbe : b.eval ((a.compile d).exec s) = b.eval s :=
      b.eval_congr _ _ (fun i hii => haf i (by omega))
    rw [hbe] at hbr
    have had := hbf d (by omega)
    rw [har] at had
    have hlen : d < ((b.compile (d + 1)).exec ((a.compile d).exec s)).length := by
      simp only [RationalProgram.exec_length]
      have := a.work_pos
      omega
    simp only [compile, RationalProgram.exec, RationalInstruction.exec,
      RationalInstruction.call, RationalCall.result, had, hbr, eval, RationalOp.eval]
    split_ifs with hab
    · rw [min_eq_left hab]
      exact ⟨had, fun i hii => (hbf i (by omega)).trans (haf i hii)⟩
    · rw [min_eq_right (le_of_not_ge hab)]
      refine ⟨rationalRegister_read_set _ d _ hlen, ?_⟩
      intro i hii
      rw [rationalRegister_read_set_ne _ d i _ (by omega), hbf i (by omega), haf i hii]

end IdentityTesting.RationalComputation
