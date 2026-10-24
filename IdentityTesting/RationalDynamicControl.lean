import IdentityTesting.RationalInstructionTraceBounds

/-! Dynamic precision and snapshot-controlled repetition. This executable
semantics records every counter operation explicitly; a binary implementation
must realize those events on a separate countdown tape. Event counts are not
themselves a bit-time certificate. -/
namespace IdentityTesting.RationalComputation

inductive RationalControlEvent where
  | arithmetic (call : RationalCall)
  | ceilSize (input : ℚ)
  | counterLoad (input : ℚ)
  | counterTest (value : ℕ)
  | counterPred (value : ℕ)
  deriving Repr

abbrev RationalControlRun := RationalRegisters × List RationalControlEvent

def controlIterate (f : RationalRegisters → RationalControlRun) : ℕ → RationalRegisters → RationalControlRun
  | 0, s => (s, [.counterTest 0])
  | n + 1, s =>
    let a := f s
    let b := controlIterate f n a.1
    (b.1, .counterTest (n + 1) :: (a.2 ++ (.counterPred (n + 1) :: b.2)))

inductive RationalControlProgram where
  | basic (p : RationalProgram)
  | seq (p q : RationalControlProgram)
  | branchLe (a b : RationalOperand) (yes no : RationalControlProgram)
  | ceilSize (dst : ℕ) (src : RationalOperand)
  | repeatRegister (countSlot : ℕ) (body : RationalControlProgram)
  deriving Repr

def RationalControlProgram.exec : RationalControlProgram → RationalRegisters → RationalRegisters
  | .basic p, s => p.exec s
  | .seq p q, s => q.exec (p.exec s)
  | .branchLe a b p q, s => if a.read s ≤ b.read s then p.exec s else q.exec s
  | .ceilSize dst src, s => s.set dst ((Nat.ceil (src.read s)).size : ℚ)
  | .repeatRegister i body, s => registerIterate body.exec (Nat.floor ((RationalOperand.reg i).read s)) s

def RationalControlProgram.run : RationalControlProgram → RationalRegisters → RationalControlRun
  | .basic p, s => ((p.run s).1, (p.run s).2.map RationalControlEvent.arithmetic)
  | .seq p q, s =>
    let a := p.run s
    let b := q.run a.1
    (b.1, a.2 ++ b.2)
  | .branchLe a b p q, s =>
    let r := if a.read s ≤ b.read s then p.run s else q.run s
    (r.1, .arithmetic ⟨.le, a.read s, b.read s⟩ :: r.2)
  | .ceilSize dst src, s =>
    (s.set dst ((Nat.ceil (src.read s)).size : ℚ), [.ceilSize (src.read s)])
  | .repeatRegister i body, s =>
    let v := (RationalOperand.reg i).read s
    let r := controlIterate body.run (Nat.floor v) s
    (r.1, .counterLoad v :: r.2)

theorem controlIterate_result (f : RationalRegisters → RationalControlRun)
    (g : RationalRegisters → RationalRegisters) (h : ∀ s, (f s).1 = g s)
    (n : ℕ) (s : RationalRegisters) : (controlIterate f n s).1 = registerIterate g n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [controlIterate, registerIterate, h] using ih (f s).1

theorem RationalControlProgram.run_result (p : RationalControlProgram) (s : RationalRegisters) :
    (p.run s).1 = p.exec s := by
  induction p generalizing s with
  | basic p => exact p.run_result s
  | seq p q hp hq => simp only [run, exec, hq, hp]
  | branchLe a b p q hp hq => simp only [run, exec]; split <;> simp_all
  | ceilSize d o => rfl
  | repeatRegister i p hp => exact controlIterate_result p.run p.exec hp _ s

theorem RationalControlProgram.exec_length (p : RationalControlProgram) (s : RationalRegisters) :
    (p.exec s).length = s.length := by
  induction p generalizing s with
  | basic p => exact p.exec_length s
  | seq p q hp hq => simp only [exec, hq, hp]
  | branchLe a b p q hp hq => simp only [exec]; split <;> simp_all
  | ceilSize d o => simp [exec]
  | repeatRegister i p hp => exact registerIterate_length p.exec hp _ s

theorem RationalControlProgram.repeatRegister_result_of_nat (i n : ℕ)
    (p : RationalControlProgram) (s : RationalRegisters)
    (h : (RationalOperand.reg i).read s = (n : ℚ)) :
    ((RationalControlProgram.repeatRegister i p).run s).1 = registerIterate p.exec n s := by
  rw [run_result]
  simp only [exec, h, Nat.floor_natCast]

theorem controlIterate_event_count (f : RationalRegisters → RationalControlRun) (C : ℕ)
    (h : ∀ s, (f s).2.length ≤ C) (n : ℕ) (s : RationalRegisters) :
    (controlIterate f n s).2.length ≤ n * (C + 2) + 1 := by
  induction n generalizing s with
  | zero => simp [controlIterate]
  | succ n ih =>
    have h1 := h s
    have h2 := ih (f s).1
    simp only [controlIterate, List.length_cons, List.length_append]
    nlinarith

theorem RationalControlProgram.repeatRegister_event_count (i n C : ℕ)
    (p : RationalControlProgram) (s : RationalRegisters)
    (hn : (RationalOperand.reg i).read s = (n : ℚ))
    (hC : ∀ t, (p.run t).2.length ≤ C) :
    ((RationalControlProgram.repeatRegister i p).run s).2.length ≤ n * (C + 2) + 2 := by
  simp only [run, hn, Nat.floor_natCast, List.length_cons]
  have h := controlIterate_event_count p.run C hC n s
  omega

end IdentityTesting.RationalComputation
