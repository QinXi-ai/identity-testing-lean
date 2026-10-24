import IdentityTesting.RationalDynamicControl
import IdentityTesting.RationalExpressionCompiler

/-! A static loop skeleton reads its repetition count from a preserved register.
The snapshot counter is separate from the body register array. -/
namespace IdentityTesting.RationalComputation

theorem RationalProgram.read_frame (p : RationalProgram) (s : RationalRegisters) (i : ℕ)
    (hi : p.slots ≤ i) : (RationalOperand.reg i).read (p.exec s) = (RationalOperand.reg i).read s := by
  induction p generalizing s with
  | skip => rfl
  | instr instr =>
    have hd : instr.dst < i := by simp only [slots] at hi; omega
    exact rationalRegister_read_set_ne s instr.dst i _ (by omega)
  | seq p q hp hq =>
    have h := max_le_iff.mp hi
    exact (hq (p.exec s) h.2).trans (hp s h.1)
  | branchLe a b p q hp hq =>
    have h : p.slots ≤ i ∧ q.slots ≤ i := by simp only [slots] at hi; omega
    simp only [exec]
    split
    · exact hp s h.1
    · exact hq s h.2
  | «repeat» n p hp =>
    change (RationalOperand.reg i).read (registerIterate p.exec n s) = _
    induction n generalizing s with
    | zero => rfl
    | succ n hn => exact (hn (p.exec s) hi).trans (hp s hi)

def RationalProgram.replaceCounts (n : ℕ) : RationalProgram → RationalProgram
  | .skip => .skip
  | .instr i => .instr i
  | .seq p q => .seq (p.replaceCounts n) (q.replaceCounts n)
  | .branchLe a b p q => .branchLe a b (p.replaceCounts n) (q.replaceCounts n)
  | .repeat _ p => .repeat n (p.replaceCounts n)

def RationalProgram.dynamicRepeats (i : ℕ) : RationalProgram → RationalControlProgram
  | .skip => .basic .skip
  | .instr j => .basic (.instr j)
  | .seq p q => .seq (p.dynamicRepeats i) (q.dynamicRepeats i)
  | .branchLe a b p q => .branchLe a b (p.dynamicRepeats i) (q.dynamicRepeats i)
  | .repeat _ p => .repeatRegister i (p.dynamicRepeats i)

theorem RationalProgram.replaceCounts_slots (p : RationalProgram) (n : ℕ) :
    (p.replaceCounts n).slots = p.slots := by
  induction p <;> simp_all [replaceCounts, slots]

theorem RationalProgram.dynamicRepeats_replaceCounts (p : RationalProgram) (i n : ℕ) :
    (p.replaceCounts n).dynamicRepeats i = p.dynamicRepeats i := by
  induction p <;> simp_all [replaceCounts, dynamicRepeats]

theorem RationalProgram.dynamicRepeats_exec (p : RationalProgram) (i n : ℕ)
    (s : RationalRegisters) (hi : p.slots ≤ i)
    (hn : (RationalOperand.reg i).read s = (n : ℚ)) :
    (p.dynamicRepeats i).exec s = (p.replaceCounts n).exec s := by
  induction p generalizing s with
  | skip => rfl
  | instr instr => rfl
  | seq p q hp hq =>
    have h := max_le_iff.mp hi
    simp only [dynamicRepeats, replaceCounts, RationalControlProgram.exec, exec]
    rw [hp s h.1 hn]
    apply hq _ h.2
    rw [(p.replaceCounts n).read_frame _ i (by simpa only [replaceCounts_slots] using h.1)]
    exact hn
  | branchLe a b p q hp hq =>
    have h : p.slots ≤ i ∧ q.slots ≤ i := by simp only [slots] at hi; omega
    simp only [dynamicRepeats, replaceCounts, RationalControlProgram.exec, exec]
    split
    · exact hp s h.1 hn
    · exact hq s h.2 hn
  | «repeat» m p hp =>
    have hiter (r : ℕ) : ∀ t, (RationalOperand.reg i).read t = (n : ℚ) →
        registerIterate (p.dynamicRepeats i).exec r t = registerIterate (p.replaceCounts n).exec r t := by
      induction r with
      | zero => intro t ht; rfl
      | succ r hr =>
        intro t ht
        simp only [registerIterate]
        rw [hp t hi ht]
        apply hr
        rw [(p.replaceCounts n).read_frame _ i (by simpa only [replaceCounts_slots] using hi)]
        exact ht
    simp only [dynamicRepeats, replaceCounts, RationalControlProgram.exec, exec, hn, Nat.floor_natCast]
    exact hiter n s hn

theorem RationalProgram.dynamicRepeats_result (p : RationalProgram) (i n : ℕ)
    (s : RationalRegisters) (hi : p.slots ≤ i)
    (hn : (RationalOperand.reg i).read s = (n : ℚ)) :
    ((p.dynamicRepeats i).run s).1 = (p.replaceCounts n).exec s := by
  rw [RationalControlProgram.run_result]
  exact p.dynamicRepeats_exec i n s hi hn

end IdentityTesting.RationalComputation
