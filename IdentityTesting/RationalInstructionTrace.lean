import IdentityTesting.RationalEncodingBounds

/-! Executable finite-register rational programs and their actual instruction
traces. The trace length counts rational instructions, not bit operations. -/
namespace IdentityTesting.RationalComputation

inductive RationalOp where
  | copy | add | sub | mul | div | le
  deriving DecidableEq, Repr

def RationalOp.eval : RationalOp → ℚ → ℚ → ℚ
  | .copy, a, _ => a
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .le, a, b => if a ≤ b then 1 else 0

inductive RationalOperand where
  | reg (index : ℕ)
  | literal (value : ℚ)
  deriving DecidableEq, Repr

abbrev RationalRegisters := List ℚ

def RationalOperand.read (s : RationalRegisters) : RationalOperand → ℚ
  | .reg i => s[i]?.getD 0
  | .literal q => q

def RationalOperand.encoding : RationalOperand → ℕ
  | .reg i => 1 + i.size
  | .literal q => 1 + rationalEncodingLength q

def RationalOperand.slots : RationalOperand → ℕ
  | .reg i => i + 1
  | .literal _ => 0

structure RationalInstruction where
  dst : ℕ
  op : RationalOp
  lhs : RationalOperand
  rhs : RationalOperand
  deriving DecidableEq, Repr

structure RationalCall where
  op : RationalOp
  lhs : ℚ
  rhs : ℚ
  deriving DecidableEq, Repr

def RationalCall.result (c : RationalCall) : ℚ := c.op.eval c.lhs c.rhs

def RationalInstruction.call (i : RationalInstruction) (s : RationalRegisters) : RationalCall :=
  ⟨i.op, i.lhs.read s, i.rhs.read s⟩

def RationalInstruction.exec (i : RationalInstruction) (s : RationalRegisters) : RationalRegisters :=
  s.set i.dst (i.call s).result

inductive RationalProgram where
  | skip
  | instr (i : RationalInstruction)
  | seq (a b : RationalProgram)
  | branchLe (a b : RationalOperand) (yes no : RationalProgram)
  | repeat (count : ℕ) (body : RationalProgram)
  deriving Repr

def registerIterate (f : RationalRegisters → RationalRegisters) : ℕ → RationalRegisters → RationalRegisters
  | 0, s => s
  | n + 1, s => registerIterate f n (f s)

def RationalProgram.exec : RationalProgram → RationalRegisters → RationalRegisters
  | .skip, s => s
  | .instr i, s => i.exec s
  | .seq a b, s => b.exec (a.exec s)
  | .branchLe a b yes no, s => if a.read s ≤ b.read s then yes.exec s else no.exec s
  | .repeat n body, s => registerIterate body.exec n s

abbrev RationalRun := RationalRegisters × List RationalCall

def traceIterate (f : RationalRegisters → RationalRun) : ℕ → RationalRegisters → RationalRun
  | 0, s => (s, [])
  | n + 1, s =>
    let a := f s
    let b := traceIterate f n a.1
    (b.1, a.2 ++ b.2)

def RationalProgram.run : RationalProgram → RationalRegisters → RationalRun
  | .skip, s => (s, [])
  | .instr i, s => (i.exec s, [i.call s])
  | .seq a b, s =>
    let x := a.run s
    let y := b.run x.1
    (y.1, x.2 ++ y.2)
  | .branchLe a b yes no, s =>
    let c : RationalCall := ⟨.le, a.read s, b.read s⟩
    let r := if c.result = 1 then yes.run s else no.run s
    (r.1, c :: r.2)
  | .repeat n body, s => traceIterate body.run n s

theorem traceIterate_result (f : RationalRegisters → RationalRun)
    (g : RationalRegisters → RationalRegisters) (h : ∀ s, (f s).1 = g s)
    (n : ℕ) (s : RationalRegisters) : (traceIterate f n s).1 = registerIterate g n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [traceIterate, registerIterate, h] using ih (f s).1

theorem RationalProgram.run_result (p : RationalProgram) (s : RationalRegisters) :
    (p.run s).1 = p.exec s := by
  induction p generalizing s with
  | skip => rfl
  | instr i => rfl
  | seq a b ha hb => simp only [run, exec, hb, ha]
  | branchLe a b yes no hy hn =>
    simp only [run, exec, RationalCall.result, RationalOp.eval]
    split <;> simp_all
  | «repeat» n body ih => exact traceIterate_result body.run body.exec ih n s

def RationalProgram.callBound : RationalProgram → ℕ
  | .skip => 0
  | .instr _ => 1
  | .seq a b => a.callBound + b.callBound
  | .branchLe _ _ yes no => 1 + max yes.callBound no.callBound
  | .repeat n body => n * body.callBound

theorem traceIterate_length (f : RationalRegisters → RationalRun) (C : ℕ)
    (h : ∀ s, (f s).2.length ≤ C) (n : ℕ) (s : RationalRegisters) :
    (traceIterate f n s).2.length ≤ n * C := by
  induction n generalizing s with
  | zero => simp [traceIterate]
  | succ n ih =>
    simp only [traceIterate, List.length_append]
    have h₁ := h s
    have h₂ := ih (f s).1
    rw [Nat.add_mul]
    omega

theorem RationalProgram.run_length (p : RationalProgram) (s : RationalRegisters) :
    (p.run s).2.length ≤ p.callBound := by
  induction p generalizing s with
  | skip => simp [run, callBound]
  | instr i => simp [run, callBound]
  | seq a b ha hb =>
    simp only [run, callBound, List.length_append]
    exact Nat.add_le_add (ha s) (hb (a.run s).1)
  | branchLe a b yes no hy hn =>
    simp only [run, callBound]
    split <;> simp only [List.length_cons]
    · exact (Nat.succ_le_succ (hy s)).trans (by omega)
    · exact (Nat.succ_le_succ (hn s)).trans (by omega)
  | «repeat» n body ih => exact traceIterate_length body.run body.callBound ih n s

def RationalProgram.encoding : RationalProgram → ℕ
  | .skip => 1
  | .instr i => 2 + i.dst.size + i.lhs.encoding + i.rhs.encoding
  | .seq a b => 1 + a.encoding + b.encoding
  | .branchLe a b yes no => 1 + a.encoding + b.encoding + yes.encoding + no.encoding
  | .repeat n body => 1 + n.size + body.encoding

def RationalProgram.slots : RationalProgram → ℕ
  | .skip => 0
  | .instr i => max (i.dst + 1) (max i.lhs.slots i.rhs.slots)
  | .seq a b => max a.slots b.slots
  | .branchLe a b yes no => max (max a.slots b.slots) (max yes.slots no.slots)
  | .repeat _ body => body.slots

def rationalRegisterEncoding (s : RationalRegisters) : ℕ :=
  s.length + (s.map rationalEncodingLength).sum

end IdentityTesting.RationalComputation
