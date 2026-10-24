import IdentityTesting.BinaryInterpreterBranchProgram
import IdentityTesting.BinaryInterpreterBranchCompareLifts
import IdentityTesting.BinaryCodeSkipActive

namespace IdentityTesting.BinaryInterpreterBranchProgram

def compareLift (frame : State) (c : BinaryInterpreterBranchCompare.State) : State :=
  {setCompare frame c with phase := .comparing}

theorem compare_step (frame : State) (c : BinaryInterpreterBranchCompare.State) (h : c.phase ≠ .halt) :
    step (compareLift frame c) = compareLift frame (BinaryInterpreterBranchCompare.step c) := by
  have hv : compareView (compareLift frame c) = c := compareView_set frame c
  change (if c.phase = .halt then afterCompare (compareLift frame c)
    else setCompare (compareLift frame c)
      (BinaryInterpreterBranchCompare.step (compareView (compareLift frame c)))) = _
  rw [if_neg h,hv]
  change {setCompare (setCompare frame c) (BinaryInterpreterBranchCompare.step c)
    with phase := .comparing} = _
  rw [setCompare_set]
  rfl

theorem forward_compare (frame : State) (c : BinaryInterpreterBranchCompare.State) (n : ℕ)
    (h : (BinaryInterpreterBranchCompare.advance n c).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (compareLift frame c) =
      afterCompare (compareLift frame (BinaryInterpreterBranchCompare.advance n c)) ∧
      bitSteps k (compareLift frame c) ≤ 2*BinaryInterpreterBranchCompare.bitSteps n c+3 := by
  induction n generalizing c with
  | zero =>
    change c.phase = .halt at h
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,compareLift,setCompare,h,BinaryInterpreterBranchCompare.advance]
    · simp [bitSteps,transitionTrace,compareLift,setCompare,h,BinaryInterpreterBranchCompare.bitSteps]
  | succ n ih =>
    by_cases hh : c.phase = .halt
    · rw [BinaryInterpreterBranchCompare.halt_advance (n+1) c hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,compareLift,setCompare,hh]
      · simp [bitSteps,transitionTrace,compareLift,setCompare,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterBranchCompare.step c) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,compare_step frame c hh]
        exact he
      · have ht := BinaryInterpreterBranchCompare.trace_active c hh
        rw [bitSteps,compare_step frame c hh]
        have hv : compareView (compareLift frame c) = c := compareView_set frame c
        simp only [transitionTrace,compareLift,setCompare,hh,if_false,List.length_cons]
        change (BinaryInterpreterBranchCompare.transitionTrace (compareView (compareLift frame c))).length+1+
          bitSteps k (compareLift frame (BinaryInterpreterBranchCompare.step c)) ≤ _
        rw [hv]
        simp only [BinaryInterpreterBranchCompare.bitSteps]
        omega

def skipLift (next : Bool) (frame : State) (s : BinaryCodeSkip.State) : State :=
  {setSkip frame s with phase := if next then .skipToNode else .skipToClose}
def afterSkip (next : Bool) (s : State) : State := if next then enterNode s else enterClosing s

theorem skip_step (next : Bool) (frame : State) (s : BinaryCodeSkip.State) (h : s.phase ≠ .halt) :
    step (skipLift next frame s) = skipLift next frame (BinaryCodeSkip.step s) := by
  cases next <;> simp [step,skipLift,setSkip,skipView,h,BinaryInterpreterDispatch.setTag]

theorem forward_skip (next : Bool) (frame : State) (s : BinaryCodeSkip.State) (n : ℕ)
    (h : (BinaryCodeSkip.advance n s).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (skipLift next frame s) =
      afterSkip next (skipLift next frame (BinaryCodeSkip.advance n s)) ∧
      bitSteps k (skipLift next frame s) ≤ 2*BinaryCodeSkip.bitSteps n s+1 := by
  induction n generalizing s with
  | zero =>
    change s.phase = .halt at h
    refine ⟨1,by omega,?_,?_⟩
    · cases next <;> simp [advance,step,skipLift,setSkip,afterSkip,h,BinaryCodeSkip.advance]
    · cases next <;> simp [bitSteps,transitionTrace,skipLift,setSkip,h,BinaryCodeSkip.bitSteps]
  | succ n ih =>
    by_cases hh : s.phase = .halt
    · rw [BinaryCodeSkip.halt_advance (n+1) s hh]
      refine ⟨1,by omega,?_,?_⟩
      · cases next <;> simp [advance,step,skipLift,setSkip,afterSkip,hh]
      · cases next <;> simp [bitSteps,transitionTrace,skipLift,setSkip,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryCodeSkip.step s) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,skip_step next frame s hh]
        exact he
      · have ht := BinaryCodeSkip.trace_active_of_eventually_halt (n+1) s hh h
        rw [bitSteps,skip_step next frame s hh]
        have hv : skipView (skipLift next frame s) = s := skipView_set frame s
        have htrace : (transitionTrace (skipLift next frame s)).length =
            (BinaryCodeSkip.transitionTrace s).length+1 := by
          cases next <;> simp [transitionTrace,skipLift,setSkip,skipView,hh,
            BinaryInterpreterDispatch.setTag]
        rw [htrace]
        simp only [BinaryCodeSkip.bitSteps]
        omega

end IdentityTesting.BinaryInterpreterBranchProgram
