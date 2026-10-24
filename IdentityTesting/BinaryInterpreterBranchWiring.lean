import IdentityTesting.BinaryInterpreterBranchLifts
import IdentityTesting.BinaryInterpreterBranchCompareRuns

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic BinaryRationalRegisters

def compareBudget (s : RationalRegisters) (lhs rhs : RationalOperand) : ℕ :=
  1000*(rationalRegisterEncoding s+s.length+lhs.slots+rhs.slots)+
    50000000*(rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1)^3

theorem compareStart_view (core : DState) (frames : List Frame)
    (hi : BinaryInterpreterDispatch.CleanIO core.io) (hp : BinaryInterpreterPool.Clean core.pool) :
    compareView (boundary .comparing (compareStart core) frames) =
      BinaryInterpreterBranchCompare.initial core.io.tape core.io.code core.io.history := by
  have hc := BinaryInterpreterDispatch.rearm_clean core hi
  have hpool := BinaryInterpreterPool.rearm_selected_initial core.pool .le hp
  simp only [compareView,boundary,compareStart]
  rw [hc]
  simp [BinaryInterpreterDispatch.execView,BinaryInterpreterDispatch.initial,
    BinaryInterpreterDispatch.initialIO_view,hpool,BinaryInterpreterOperandExecute.pairView,
    BinaryInterpreterBranchCompare.initial,BinaryInterpreterBranchCompare.loadingState,
    BinaryInterpreterOperandPair.initial,BinaryInterpreterOperand.initial,
    BinaryInterpreterDispatch.initialIO,BinaryInterpreterDispatch.IO.view,
    BinaryInterpreterDispatch.IO.ofExec,BinaryInterpreterOperandExecute.initial,
    BinaryInterpreterArithmeticClean.runningState,BinaryInterpreterArithmetic.operatingState,
    BinaryInterpreterLiteralInput.initial]

theorem setCompare_clean (frame : State) (c : BinaryInterpreterBranchCompare.State)
    (hi : BinaryInterpreterDispatch.CleanIO frame.core.io)
    (hc : BinaryInterpreterOperand.Clean c.pair.loader) :
    BinaryInterpreterDispatch.CleanIO (setCompare frame c).core.io := by
  rcases hi with ⟨_,_,hr,hd,_,_,_,_,_⟩
  rcases hc with ⟨ht,ha,hs,hcp,hrec,hn,hden⟩
  exact ⟨ht,ha,hr,hd,hs,hcp,hrec,hn,hden⟩

theorem setCompare_pool_clean (frame : State) (c : BinaryInterpreterBranchCompare.State)
    (hp : BinaryInterpreterPool.Clean frame.core.pool)
    (hc : ∀ i, BinaryInterpreterBranchCompare.storage.tapes (BinaryInterpreterBranchCompare.core c) i = []) :
    BinaryInterpreterPool.Clean (setCompare frame c).core.pool := by
  intro op i
  by_cases h : op = .le
  · subst op
    simpa [setCompare,BinaryInterpreterDispatch.setExec,BinaryInterpreterOperandExecute.setPair,
      BinaryInterpreterPool.get_set,BinaryInterpreterBranchCompare.core,BinaryInterpreterBranchCompare.pairCore] using hc i
  · simpa [setCompare,BinaryInterpreterDispatch.setExec,BinaryInterpreterPool.other_set,
      h] using hp op i

theorem compare_run (core : DState) (frames : List Frame) (s : RationalRegisters)
    (lhs rhs : RationalOperand) (hi : BinaryInterpreterDispatch.CleanIO core.io)
    (hp : BinaryInterpreterPool.Clean core.pool) (ht : core.io.tape = tape s)
    (code : List Symbol)
    (hcode : core.io.code = RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length) :
    ∃ n f,
      advance n (boundary .comparing (compareStart core) frames) =
        (if lhs.read s ≤ rhs.read s then boundary .node (resetTag f) (.skipElse::frames)
          else boundary .skipToNode (resetTag f) (.close::frames)) ∧
      f.io.tape = tape s ∧ BinaryInterpreterDispatch.CleanIO f.io ∧
      BinaryInterpreterPool.Clean f.pool ∧ f.io.code = code ∧
      f.io.history = (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs).reverse ++ core.io.history ∧
      bitSteps n (boundary .comparing (compareStart core) frames) ≤ 2*compareBudget s lhs rhs+3 := by
  let start := boundary .comparing (compareStart core) frames
  let ci := BinaryInterpreterBranchCompare.initial (tape s)
    (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) core.io.history
  have hv : compareView start = ci := by
    simpa only [ht,hcode] using compareStart_view core frames hi hp
  have hstart : compareLift start ci = start := by
    rw [← hv]
    simp only [compareLift,setCompare_view]
    rfl
  obtain ⟨nc,hfinished,hcost⟩ := BinaryInterpreterBranchCompare.binary_branch_compare s lhs rhs hl hr code core.io.history
  let cf := BinaryInterpreterBranchCompare.advance nc ci
  change BinaryInterpreterBranchCompare.Finished s lhs rhs code core.io.history cf at hfinished
  rcases hfinished with ⟨hh,hd,hft,hfc,hfh,hfi,hfp,_⟩
  obtain ⟨k,_,he,hk⟩ := forward_compare start ci nc hh
  rw [hstart] at he hk
  let f := (setCompare start cf).core
  have hcontrol : afterCompare (compareLift start cf) =
      (if lhs.read s ≤ rhs.read s then boundary .node (resetTag f) (.skipElse::frames)
        else boundary .skipToNode (resetTag f) (.close::frames)) := by
    unfold afterCompare
    change (if cf.decision then _ else _) = _
    rw [hd]
    by_cases hcond : lhs.read s ≤ rhs.read s <;>
      simp only [hcond,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] <;> rfl
  refine ⟨k,f,he.trans hcontrol,hft,?_,?_,hfc,hfh,?_⟩
  · apply setCompare_clean start cf _ hfi
    exact hi
  · apply setCompare_pool_clean start cf _ hfp
    exact BinaryInterpreterPool.rearm_clean core.pool .le hp
  · change BinaryInterpreterBranchCompare.bitSteps nc ci ≤ compareBudget s lhs rhs at hcost
    change bitSteps k start ≤ 2*compareBudget s lhs rhs+3
    omega

end IdentityTesting.BinaryInterpreterBranchProgram
