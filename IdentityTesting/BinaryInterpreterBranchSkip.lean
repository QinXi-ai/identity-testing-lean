import IdentityTesting.BinaryInterpreterBranchLifts
import IdentityTesting.BinaryCodeSkipRuns

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation

/-- Specification of the exact I/O suffix after consuming a code segment. -/
def afterCode (core : DState) (consumed suffix : List Symbol) : DState :=
  {core with io := {core.io with code := suffix,history := consumed.reverse ++ core.io.history}}

/-- The physical skipper consumes one unchosen subtree and preserves the
register bank, workspace pools, cursors, and branch continuation stack. -/
theorem skip_program (core : DState) (frames : List Frame) (next : Bool)
    (p : RationalProgram) (suffix : List Symbol)
    (hcode : core.io.code = RationalProgramCode.program p ++ suffix) :
    ∃ k,
      advance k (boundary (if next then .skipToNode else .skipToClose)
        (resetTag core) frames) =
        boundary (if next then .node else .closing)
          (resetTag (afterCode core (RationalProgramCode.program p) suffix)) frames ∧
      bitSteps k (boundary (if next then .skipToNode else .skipToClose)
        (resetTag core) frames) ≤ 80*((RationalProgramCode.program p).length+1)+1 := by
  obtain ⟨n,he,hc⟩ := BinaryCodeSkip.binary_skip_program p suffix core.io.history
  have hh : (BinaryCodeSkip.advance n
      (BinaryCodeSkip.initial (RationalProgramCode.program p ++ suffix) core.io.history)).phase = .halt := by
    rw [he]
    rfl
  obtain ⟨k,_,hk,hb⟩ := forward_skip next (boundary .node core frames) _ n hh
  have hstart : skipLift next (boundary .node core frames)
      (BinaryCodeSkip.initial (RationalProgramCode.program p ++ suffix) core.io.history) =
      boundary (if next then .skipToNode else .skipToClose) (resetTag core) frames := by
    rw [← hcode]
    rfl
  rw [hstart] at hk hb
  rw [he] at hk
  refine ⟨k,?_,by omega⟩
  cases next <;> simpa [afterSkip,skipLift,setSkip,boundary,BinaryCodeSkip.haltState,BinaryCodeSkip.ready,
    enterNode,enterClosing,control,resetTag,BinaryInterpreterProgram.resetTag,
    BinaryInterpreterDispatch.setTag,afterCode] using hk

end IdentityTesting.BinaryInterpreterBranchProgram
