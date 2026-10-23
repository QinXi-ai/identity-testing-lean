import IdentityTesting.RationalInstructionTraceBounds

/-! Relocation places a rational program behind a fixed control-register prefix.
The executed calls are unchanged and the prefix is preserved. -/
namespace IdentityTesting.RationalComputation

def RationalOperand.shift (d : ℕ) : RationalOperand → RationalOperand
  | .reg i => .reg (d + i)
  | .literal q => .literal q

def RationalInstruction.shift (d : ℕ) (i : RationalInstruction) : RationalInstruction :=
  ⟨d + i.dst, i.op, i.lhs.shift d, i.rhs.shift d⟩

def RationalProgram.shift (d : ℕ) : RationalProgram → RationalProgram
  | .skip => .skip
  | .instr i => .instr (i.shift d)
  | .seq p q => .seq (p.shift d) (q.shift d)
  | .branchLe a b p q => .branchLe (a.shift d) (b.shift d) (p.shift d) (q.shift d)
  | .repeat n p => .repeat n (p.shift d)

theorem RationalOperand.shift_read (o : RationalOperand) (pre s : RationalRegisters) :
    (o.shift pre.length).read (pre ++ s) = o.read s := by
  cases o with
  | literal q => rfl
  | reg i =>
    simp only [shift, read]
    rw [List.getElem?_append_right (by omega)]
    simp

theorem RationalInstruction.shift_call (i : RationalInstruction) (pre s : RationalRegisters) :
    (i.shift pre.length).call (pre ++ s) = i.call s := by
  simp only [shift, call, RationalOperand.shift_read]

theorem RationalInstruction.shift_exec (i : RationalInstruction) (pre s : RationalRegisters) :
    (i.shift pre.length).exec (pre ++ s) = pre ++ i.exec s := by
  change (pre ++ s).set (pre.length + i.dst) ((i.shift pre.length).call (pre ++ s)).result =
    pre ++ s.set i.dst (i.call s).result
  rw [shift_call, List.set_append_right _ _ (by omega)]
  simp

theorem traceIterate_prefix (f g : RationalRegisters → RationalRun) (pre : RationalRegisters)
    (h : ∀ s, f (pre ++ s) = (pre ++ (g s).1, (g s).2)) (n : ℕ) (s : RationalRegisters) :
    traceIterate f n (pre ++ s) = (pre ++ (traceIterate g n s).1, (traceIterate g n s).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [traceIterate, h, ih]

theorem RationalProgram.shift_run (p : RationalProgram) (pre s : RationalRegisters) :
    (p.shift pre.length).run (pre ++ s) = (pre ++ (p.run s).1, (p.run s).2) := by
  induction p generalizing s with
  | skip => rfl
  | instr i => simp only [shift, run, RationalInstruction.shift_exec, RationalInstruction.shift_call]
  | seq p q hp hq => simp only [shift, run, hp, hq]
  | branchLe a b p q hp hq =>
    simp only [shift, run, RationalOperand.shift_read]
    split <;> simp_all
  | «repeat» n p hp => exact traceIterate_prefix _ _ pre hp n s

theorem RationalProgram.shift_exec (p : RationalProgram) (pre s : RationalRegisters) :
    (p.shift pre.length).exec (pre ++ s) = pre ++ p.exec s := by
  simpa only [run_result] using congrArg Prod.fst (p.shift_run pre s)

theorem RationalProgram.shift_callBound (p : RationalProgram) (d : ℕ) :
    (p.shift d).callBound = p.callBound := by
  induction p with
  | skip => rfl
  | instr i => rfl
  | seq p q hp hq => simp only [shift, callBound, hp, hq]
  | branchLe a b p q hp hq => simp only [shift, callBound, hp, hq]
  | «repeat» n p hp => simp only [shift, callBound, hp]

end IdentityTesting.RationalComputation
