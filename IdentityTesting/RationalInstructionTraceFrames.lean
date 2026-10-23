import IdentityTesting.RationalInstructionTraceBounds

/-! Finite-register frame rule for composing actual arithmetic programs. -/
namespace IdentityTesting.RationalComputation

theorem RationalOperand.read_append (a : RationalOperand) (s t : RationalRegisters)
    (h : a.slots ≤ s.length) : a.read (s ++ t) = a.read s := by
  cases a with
  | literal q => rfl
  | reg i =>
    have hi : i < s.length := by simpa only [RationalOperand.slots] using h
    simp only [RationalOperand.read, List.getElem?_append_left hi]

theorem traceIterate_append (f : RationalRegisters → RationalRun) (B : ℕ)
    (hlen : ∀ s, (f s).1.length = s.length)
    (hf : ∀ s t, B ≤ s.length → f (s ++ t) = ((f s).1 ++ t, (f s).2))
    (n : ℕ) (s t : RationalRegisters) (h : B ≤ s.length) :
    traceIterate f n (s ++ t) = ((traceIterate f n s).1 ++ t, (traceIterate f n s).2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [traceIterate, hf s t h]
    rw [ih (f s).1 (by simpa only [hlen] using h)]

theorem RationalProgram.run_append (p : RationalProgram) (s t : RationalRegisters)
    (h : p.slots ≤ s.length) : p.run (s ++ t) = ((p.run s).1 ++ t, (p.run s).2) := by
  induction p generalizing s t with
  | skip => rfl
  | instr i =>
    have hd : i.dst < s.length := RationalInstruction.destination_in_bounds i s h
    have hl : i.lhs.slots ≤ s.length := (le_max_left _ _).trans
      ((le_max_right _ _).trans h)
    have hr : i.rhs.slots ≤ s.length := (le_max_right _ _).trans
      ((le_max_right _ _).trans h)
    simp only [run, RationalInstruction.exec, RationalInstruction.call,
      i.lhs.read_append s t hl, i.rhs.read_append s t hr, List.set_append_left _ _ hd]
  | seq a b ha hb =>
    have hab := max_le_iff.mp h
    simp only [run, ha s t hab.1]
    rw [hb (a.run s).1 t (by simpa only [a.run_register_length] using hab.2)]
  | branchLe a b yes no hy hn =>
    have hab := max_le_iff.mp h
    have ha := (max_le_iff.mp hab.1).1
    have hb := (max_le_iff.mp hab.1).2
    have hyes := (max_le_iff.mp hab.2).1
    have hno := (max_le_iff.mp hab.2).2
    simp only [run, a.read_append s t ha, b.read_append s t hb]
    split
    · rw [hy s t hyes]
    · rw [hn s t hno]
  | «repeat» n body ih =>
    exact traceIterate_append body.run body.slots body.run_register_length
      (fun s t hs => ih s t hs) n s t h

end IdentityTesting.RationalComputation
