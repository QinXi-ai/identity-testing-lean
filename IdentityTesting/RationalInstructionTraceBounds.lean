import IdentityTesting.RationalInstructionTrace

/-! The interpreter preserves its finite register array. The bounds expose
storage separately from instruction count and rational operand lengths. -/
namespace IdentityTesting.RationalComputation

theorem registerIterate_length (f : RationalRegisters → RationalRegisters)
    (h : ∀ s, (f s).length = s.length) (n : ℕ) (s : RationalRegisters) :
    (registerIterate f n s).length = s.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [registerIterate, ih, h]

theorem RationalProgram.exec_length (p : RationalProgram) (s : RationalRegisters) :
    (p.exec s).length = s.length := by
  induction p generalizing s with
  | skip => rfl
  | instr i => simp [exec, RationalInstruction.exec]
  | seq a b ha hb => simp only [exec, hb, ha]
  | branchLe a b yes no hy hn => simp only [exec]; split <;> simp_all
  | «repeat» n body ih => exact registerIterate_length body.exec ih n s

theorem RationalProgram.run_register_length (p : RationalProgram) (s : RationalRegisters) :
    (p.run s).1.length = s.length := by rw [p.run_result, p.exec_length]

theorem RationalOperand.reg_read (s : RationalRegisters) (i : ℕ) (hi : i < s.length) :
    (RationalOperand.reg i).read s = s[i] := by simp [RationalOperand.read, hi]

theorem RationalInstruction.destination_in_bounds (p : RationalInstruction)
    (s : RationalRegisters)
    (h : (RationalProgram.instr p).slots ≤ s.length) : p.dst < s.length := by
  simp only [RationalProgram.slots, max_le_iff] at h
  omega

end IdentityTesting.RationalComputation
