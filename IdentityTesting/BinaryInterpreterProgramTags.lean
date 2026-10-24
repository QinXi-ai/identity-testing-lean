import IdentityTesting.BinaryInterpreterProgram

namespace IdentityTesting.BinaryInterpreterProgram
open BinaryRegisterMachine RationalComputation

def afterTag (core : DState) (a b c : Bool) (code : List Symbol) : DState :=
  BinaryInterpreterDispatch.setTag core
    ⟨.halt,code,(RationalProgramCode.tag a b c).reverse ++ core.io.history,a,b,c⟩

theorem resetTag_as_loader (core : DState) (a b c : Bool) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.tag a b c ++ code) :
    resetTag core = BinaryInterpreterDispatch.setTag core
      (BinaryCodeTagDecoder.initial (RationalProgramCode.tag a b c ++ code) core.io.history) := by
  rw [← h]
  rfl

theorem node_tag_run (core : DState) (frames : List Frame) (a b c : Bool) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.tag a b c ++ code) :
    advance 5 ⟨.node,resetTag core,frames⟩ = dispatchNode ⟨.node,afterTag core a b c code,frames⟩ := by
  rw [resetTag_as_loader core a b c code h]
  simp [advance,step,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,RationalProgramCode.tag,
    RationalProgramCode.word,afterTag]

theorem node_tag_cost (core : DState) (frames : List Frame) (a b c : Bool) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.tag a b c ++ code) :
    bitSteps 5 ⟨.node,resetTag core,frames⟩ = 35 := by
  rw [resetTag_as_loader core a b c code h]
  simp [bitSteps,transitionTrace,step,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,BinaryCodeTagDecoder.transitionTrace,
    RationalProgramCode.tag,RationalProgramCode.word]

theorem close_tag_run (core : DState) (frames : List Frame) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.endTag ++ code) :
    advance 5 ⟨.closing,resetTag core,frames⟩ = ⟨.returning,afterTag core true true true code,frames⟩ := by
  rw [resetTag_as_loader core true true true code h]
  simp [advance,step,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,RationalProgramCode.tag,
    RationalProgramCode.word,afterTag]

theorem close_tag_cost (core : DState) (frames : List Frame) (code : List Symbol)
    (h : core.io.code = RationalProgramCode.endTag ++ code) :
    bitSteps 5 ⟨.closing,resetTag core,frames⟩ = 33 := by
  rw [resetTag_as_loader core true true true code h]
  simp [bitSteps,transitionTrace,step,BinaryInterpreterDispatch.setTag,BinaryInterpreterDispatch.tagView,
    BinaryCodeTagDecoder.initial,BinaryCodeTagDecoder.step,BinaryCodeTagDecoder.transitionTrace,
    RationalProgramCode.tag,RationalProgramCode.word]

theorem afterTag_clean (core : DState) (a b c : Bool) (code : List Symbol)
    (h : BinaryInterpreterDispatch.CleanIO core.io) :
    BinaryInterpreterDispatch.CleanIO (afterTag core a b c code).io := h

end IdentityTesting.BinaryInterpreterProgram
