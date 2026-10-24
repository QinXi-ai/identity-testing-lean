import IdentityTesting.RationalDynamicRepeat

/-! Dynamic-control arithmetic traces agree with the instantiated static
program. Counter and ceil-size events remain separately visible. -/
namespace IdentityTesting.RationalComputation

def RationalControlEvent.arithmeticCall : RationalControlEvent → Option RationalCall
  | .arithmetic c => some c
  | _ => none

def arithmeticCalls (events : List RationalControlEvent) : List RationalCall :=
  events.filterMap RationalControlEvent.arithmeticCall

theorem arithmeticCalls_append (a b : List RationalControlEvent) :
    arithmeticCalls (a ++ b) = arithmeticCalls a ++ arithmeticCalls b := List.filterMap_append

theorem arithmeticCalls_map (cs : List RationalCall) :
    arithmeticCalls (cs.map RationalControlEvent.arithmetic) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa only [arithmeticCalls, List.map_cons, List.filterMap_cons,
      RationalControlEvent.arithmeticCall] using congrArg (List.cons c) ih

theorem controlIterate_arithmeticCalls (f : RationalRegisters → RationalControlRun)
    (g : RationalRegisters → RationalRun) (P : RationalRegisters → Prop)
    (hres : ∀ s, P s → (f s).1 = (g s).1)
    (hcall : ∀ s, P s → arithmeticCalls (f s).2 = (g s).2)
    (hpres : ∀ s, P s → P (g s).1) (n : ℕ) (s : RationalRegisters) (hs : P s) :
    arithmeticCalls (controlIterate f n s).2 = (traceIterate g n s).2 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [controlIterate, arithmeticCalls, List.filterMap_cons, List.filterMap_append,
      RationalControlEvent.arithmeticCall, traceIterate]
    change arithmeticCalls (f s).2 ++ arithmeticCalls (controlIterate f n (f s).1).2 = _
    rw [hcall s hs, hres s hs, ih (g s).1 (hpres s hs)]

theorem RationalProgram.dynamicRepeats_calls (p : RationalProgram) (i n : ℕ)
    (s : RationalRegisters) (hi : p.slots ≤ i)
    (hn : (RationalOperand.reg i).read s = (n : ℚ)) :
    arithmeticCalls ((p.dynamicRepeats i).run s).2 = ((p.replaceCounts n).run s).2 := by
  induction p generalizing s with
  | skip => rfl
  | instr instr => rfl
  | seq p q hp hq =>
    have h := max_le_iff.mp hi
    have hr := p.dynamicRepeats_result i n s h.1 hn
    simp only [dynamicRepeats, replaceCounts, RationalControlProgram.run, RationalProgram.run,
      arithmeticCalls_append, hr, RationalProgram.run_result]
    rw [hp s h.1 hn]
    apply congrArg (List.append ((p.replaceCounts n).run s).2)
    apply hq _ h.2
    rw [(p.replaceCounts n).read_frame _ i (by simpa only [replaceCounts_slots] using h.1)]
    exact hn
  | branchLe a b p q hp hq =>
    have h : p.slots ≤ i ∧ q.slots ≤ i := by simp only [slots] at hi; omega
    by_cases hab : a.read s ≤ b.read s
    · simp only [dynamicRepeats, replaceCounts, RationalControlProgram.run, RationalProgram.run,
        RationalCall.result, RationalOp.eval, hab, if_true, arithmeticCalls, List.filterMap_cons,
        RationalControlEvent.arithmeticCall]
      exact congrArg (List.cons _) (hp s h.1 hn)
    · simp only [dynamicRepeats, replaceCounts, RationalControlProgram.run, RationalProgram.run,
        RationalCall.result, RationalOp.eval, hab, if_false, zero_ne_one, arithmeticCalls,
        List.filterMap_cons, RationalControlEvent.arithmeticCall]
      exact congrArg (List.cons _) (hq s h.2 hn)
  | «repeat» m p hp =>
    simp only [dynamicRepeats, replaceCounts, RationalControlProgram.run, RationalProgram.run,
      hn, Nat.floor_natCast, arithmeticCalls, List.filterMap_cons, RationalControlEvent.arithmeticCall]
    apply controlIterate_arithmeticCalls (p.dynamicRepeats i).run (p.replaceCounts n).run
      (fun t => (RationalOperand.reg i).read t = (n : ℚ))
    · intro t ht
      rw [p.dynamicRepeats_result i n t hi ht, RationalProgram.run_result]
    · intro t ht; exact hp t hi ht
    · intro t ht
      rw [RationalProgram.run_result,
        (p.replaceCounts n).read_frame t i (by simpa only [replaceCounts_slots] using hi)]
      exact ht
    · exact hn

end IdentityTesting.RationalComputation
