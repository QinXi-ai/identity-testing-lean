import IdentityTesting.RationalDynamicControl
import IdentityTesting.RationalInstructionTraceRelocation

/-! Relocation of the actual dynamic-control program preserves every event,
including loaded counters and ceil-size inputs. -/
namespace IdentityTesting.RationalComputation

def RationalControlProgram.shift (d : ℕ) : RationalControlProgram → RationalControlProgram
  | .basic p => .basic (p.shift d)
  | .seq p q => .seq (p.shift d) (q.shift d)
  | .branchLe a b p q => .branchLe (a.shift d) (b.shift d) (p.shift d) (q.shift d)
  | .ceilSize i a => .ceilSize (d + i) (a.shift d)
  | .repeatRegister i p => .repeatRegister (d + i) (p.shift d)

theorem controlIterate_prefix (f g : RationalRegisters → RationalControlRun) (pre : RationalRegisters)
    (h : ∀ s, f (pre ++ s) = (pre ++ (g s).1, (g s).2)) (n : ℕ) (s : RationalRegisters) :
    controlIterate f n (pre ++ s) = (pre ++ (controlIterate g n s).1, (controlIterate g n s).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [controlIterate, h, ih]

theorem RationalControlProgram.shift_run (p : RationalControlProgram) (pre s : RationalRegisters) :
    (p.shift pre.length).run (pre ++ s) = (pre ++ (p.run s).1, (p.run s).2) := by
  induction p generalizing s with
  | basic p => simp only [shift, run, RationalProgram.shift_run]
  | seq p q hp hq => simp only [shift, run, hp, hq]
  | branchLe a b p q hp hq =>
    simp only [shift, run, RationalOperand.shift_read]
    split <;> simp_all
  | ceilSize i a =>
    simp only [shift, run, RationalOperand.shift_read,
      List.set_append_right _ _ (show pre.length ≤ pre.length + i by omega)]
    simp
  | repeatRegister i p hp =>
    have hr := (RationalOperand.reg i).shift_read pre s
    change (RationalOperand.reg (pre.length + i)).read (pre ++ s) =
      (RationalOperand.reg i).read s at hr
    simp only [shift, run, hr, controlIterate_prefix _ _ pre hp]

theorem RationalControlProgram.shift_exec (p : RationalControlProgram) (pre s : RationalRegisters) :
    (p.shift pre.length).exec (pre ++ s) = pre ++ p.exec s := by
  simpa only [run_result] using congrArg Prod.fst (p.shift_run pre s)

end IdentityTesting.RationalComputation
