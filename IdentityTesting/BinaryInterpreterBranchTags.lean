import IdentityTesting.BinaryInterpreterBranchProgram
import IdentityTesting.BinaryInterpreterProgramTags

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation
abbrev afterTag := BinaryInterpreterProgram.afterTag

theorem node_tag_run (core : DState) (frames : List Frame) (a b c : Bool) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.tag a b c ++ code) :
    advance 5 (boundary .node (resetTag core) frames) = dispatchNode (boundary .node (afterTag core a b c code) frames) := by
  rw [resetTag,BinaryInterpreterProgram.resetTag_as_loader core a b c code h]
  simp [advance,step,boundary,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,RationalProgramCode.tag,
    RationalProgramCode.word,afterTag,BinaryInterpreterProgram.afterTag]

theorem node_tag_cost (core : DState) (frames : List Frame) (a b c : Bool) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.tag a b c ++ code) :
    bitSteps 5 (boundary .node (resetTag core) frames) = 35 := by
  rw [resetTag,BinaryInterpreterProgram.resetTag_as_loader core a b c code h]
  simp [bitSteps,transitionTrace,step,boundary,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,BinaryCodeTagDecoder.transitionTrace,
    RationalProgramCode.tag,RationalProgramCode.word]

theorem close_tag_run (core : DState) (frames : List Frame) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.endTag ++ code) :
    advance 5 (boundary .closing (resetTag core) frames) = boundary .returning (afterTag core true true true code) frames := by
  rw [resetTag,BinaryInterpreterProgram.resetTag_as_loader core true true true code h]
  simp [advance,step,boundary,control,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,RationalProgramCode.tag,
    RationalProgramCode.word,afterTag,BinaryInterpreterProgram.afterTag]

theorem close_tag_cost (core : DState) (frames : List Frame) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.endTag ++ code) :
    bitSteps 5 (boundary .closing (resetTag core) frames) = 33 := by
  rw [resetTag,BinaryInterpreterProgram.resetTag_as_loader core true true true code h]
  simp [bitSteps,transitionTrace,step,boundary,control,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,BinaryCodeTagDecoder.transitionTrace,
    RationalProgramCode.tag,RationalProgramCode.word]

theorem forward_instruction (frames : List Frame) (d : DState) (n : ℕ)
    (h : BinaryInterpreterDispatch.Done (BinaryInterpreterDispatch.advance n d)) :
    ∃ k, k ≤ n+1 ∧ advance k (boundary .instruction d frames) =
      boundary .returning (BinaryInterpreterDispatch.advance n d) frames ∧
      bitSteps k (boundary .instruction d frames) ≤ 2*BinaryInterpreterDispatch.bitSteps n d+1 := by
  induction n generalizing d with
  | zero =>
    change BinaryInterpreterDispatch.Done d at h
    refine ⟨1,by omega,?_,?_⟩
    · simp [advance,step,boundary,control,h,BinaryInterpreterDispatch.advance]
    · simp [bitSteps,transitionTrace,boundary,h,BinaryInterpreterDispatch.bitSteps]
  | succ n ih =>
    by_cases hh : BinaryInterpreterDispatch.Done d
    · rw [BinaryInterpreterDispatch.done_advance (n+1) d hh]
      refine ⟨1,by omega,?_,?_⟩
      · simp [advance,step,boundary,control,hh]
      · simp [bitSteps,transitionTrace,boundary,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterDispatch.step d) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance]
        simpa only [step,boundary,if_neg hh,BinaryInterpreterDispatch.advance] using he
      · have hi := BinaryInterpreterDispatch.eventually_done_not_invalid (n+1) d h
        have ht := BinaryInterpreterDispatch.trace_active_of_not_invalid d hi hh
        simp only [bitSteps,transitionTrace,step,boundary,if_neg hh,List.length_cons,BinaryInterpreterDispatch.bitSteps]
        change (BinaryInterpreterDispatch.transitionTrace d).length+1+
          bitSteps k (boundary .instruction (BinaryInterpreterDispatch.step d) frames) ≤ _
        omega

end IdentityTesting.BinaryInterpreterBranchProgram
