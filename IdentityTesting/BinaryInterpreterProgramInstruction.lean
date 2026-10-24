import IdentityTesting.BinaryInterpreterProgram

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryInterpreterArithmetic

theorem done_advance (n : ℕ) (s : State) (h : Done s) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [advance,done_step s h] using ih

theorem invalid_advance (n : ℕ) (s : State) (h : s.phase = .invalid) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [advance,step,h] using ih

theorem eventually_done_not_invalid (n : ℕ) (s : State) (h : Done (advance n s)) :
    s.phase ≠ .invalid := by
  intro hi
  rw [invalid_advance n s hi] at h
  have hp := h.1
  rw [hi] at hp
  contradiction

theorem clean_trace_active {L : BinaryInterpreterLayout.Layout} (W : BinaryInterpreterStorage.Storage L)
    (s : BinaryInterpreterArithmeticClean.State W) (h : s.phase ≠ .halt) :
    1 ≤ (BinaryInterpreterArithmeticClean.transitionTrace W s).length := by
  cases hp : s.phase <;> simp only [BinaryInterpreterArithmeticClean.transitionTrace,hp]
  · split <;> simp
  · split <;> simp
  · exact False.elim (h hp)

/-- The inactive error label is excluded by eventual termination. Every other
nonfinished state has an actual branch or symbol action in its defined trace. -/
theorem trace_active_of_not_invalid (s : State) (hi : s.phase ≠ .invalid) (h : ¬Done s) :
    1 ≤ (transitionTrace s).length := by
  cases hp : s.phase with
  | tag => simp only [transitionTrace,hp]; split <;> simp
  | address => simp only [transitionTrace,hp]; split <;> simp
  | invalid => exact False.elim (hi hp)
  | running =>
    cases hl : s.io.loading with
    | true =>
      simp only [transitionTrace,hp,BinaryInterpreterOperandExecute.transitionTrace,execView,IO.view,hl,if_true]
      split <;> simp
    | false =>
      have he : (execView s s.selected).execution.phase ≠ .halt := by
        intro he
        exact h ⟨hp,hl,he⟩
      have hl' : (execView s s.selected).loading = false := hl
      simp only [transitionTrace,hp,BinaryInterpreterOperandExecute.transitionTrace,hl',Bool.false_eq_true,if_false]
      exact clean_trace_active (arithmeticStorage s.selected) (execView s s.selected).execution he

end IdentityTesting.BinaryInterpreterDispatch

namespace IdentityTesting.BinaryInterpreterProgram

/-- Lift an actual instruction run into the outer program controller. The
factor two pays for the real additional branch at each active inner step. -/
theorem forward_instruction (frames : List Frame) (d : DState) (n : ℕ)
    (h : BinaryInterpreterDispatch.Done (BinaryInterpreterDispatch.advance n d)) :
    ∃ k, k ≤ n+1 ∧
      advance k ⟨.instruction,d,frames⟩ =
        ⟨.returning,BinaryInterpreterDispatch.advance n d,frames⟩ ∧
      bitSteps k ⟨.instruction,d,frames⟩ ≤ 2*BinaryInterpreterDispatch.bitSteps n d+1 := by
  induction n generalizing d with
  | zero =>
    change BinaryInterpreterDispatch.Done d at h
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,h,BinaryInterpreterDispatch.advance]
    · simp [bitSteps,transitionTrace,h,BinaryInterpreterDispatch.bitSteps]
  | succ n ih =>
    by_cases hh : BinaryInterpreterDispatch.Done d
    · rw [BinaryInterpreterDispatch.done_advance (n+1) d hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,hh]
      · simp [bitSteps,transitionTrace,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterDispatch.step d) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance]
        simpa only [step,if_neg hh,BinaryInterpreterDispatch.advance] using he
      · have hi := BinaryInterpreterDispatch.eventually_done_not_invalid (n+1) d h
        have ht := BinaryInterpreterDispatch.trace_active_of_not_invalid d hi hh
        simp only [bitSteps,transitionTrace,step,if_neg hh,List.length_cons,BinaryInterpreterDispatch.bitSteps]
        change (BinaryInterpreterDispatch.transitionTrace d).length+1+
          bitSteps k ⟨.instruction,BinaryInterpreterDispatch.step d,frames⟩ ≤ _
        omega

end IdentityTesting.BinaryInterpreterProgram
