import IdentityTesting.BinaryInterpreterBranchCompareLifts

namespace IdentityTesting.BinaryInterpreterBranchCompare
open BinaryRegisterMachine BinaryInterpreterArithmetic BinaryInterpreterStorage RationalComputation BinaryRationalRegisters

def Finished (s : RationalRegisters) (lhs rhs : RationalOperand) (code history : List Symbol) (f : State) : Prop :=
  f.phase = .halt ∧ f.decision = decide (lhs.read s ≤ rhs.read s) ∧
  f.pair.loader.tape = tape s ∧ f.pair.loader.data.code = code ∧
  f.pair.loader.data.history = (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs).reverse ++ history ∧
  BinaryInterpreterOperand.Clean f.pair.loader ∧
  (∀ i, storage.tapes (core f) i = []) ∧ f.cursor.val = 0

/-- This entry has no destination register and never invokes a writer. Both
operand fields are consumed from the actual code tape; the concrete comparison
machine supplies correctness and termination before its core is cleared. -/
theorem binary_branch_compare (s : RationalRegisters) (lhs rhs : RationalOperand)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length) (code history : List Symbol) :
    ∃ n,
      let start := initial (tape s) (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history
      Finished s lhs rhs code history (advance n start) ∧
      bitSteps n start ≤ 1000*(rationalRegisterEncoding s+s.length+lhs.slots+rhs.slots)+
        50000000*(rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1)^3 := by
  let source := RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code
  let p := BinaryInterpreterOperandPair.initial layout (tape s) source history
  let start := initial (tape s) source history
  obtain ⟨np,hnp,hp⟩ := BinaryInterpreterOperandPair.pair_run (arithmeticInputLocal .le) s lhs rhs hl hr code history
  let pf := BinaryInterpreterOperandPair.advance np p
  change BinaryInterpreterOperandPair.Loaded s lhs rhs code history pf at hp
  rcases hp with ⟨hph,hpc,hpt,hpcode,hphistory,hpclean⟩
  let c := layout.initial (BinaryRationalArithmetic.encode (lhs.read s)) (BinaryRationalArithmetic.encode (rhs.read s))
  change pairCore pf = c at hpc
  obtain ⟨kl,_,hel,hcl⟩ := forward_load p np hph
  change advance kl start = operatingState pf (pairCore pf) at hel
  rw [hpc] at hel
  change bitSteps kl start ≤ 17*np+1 at hcl
  obtain ⟨nm,hm,hz,hcost⟩ := actual_local_run .le (lhs.read s) (rhs.read s)
  change layout.halted (layout.advance nm c) = true at hm
  change layout.output (layout.advance nm c) = BinaryRationalArithmetic.encode (RationalOp.le.eval (lhs.read s) (rhs.read s)) at hz
  change layout.bitSteps nm c ≤ _ at hcost
  let cf := layout.advance nm c
  obtain ⟨ko,_,heo,hco⟩ := forward_operate pf c nm hm
  have hdecision : readDecision cf = decide (lhs.read s ≤ rhs.read s) := readDecision_of_output cf _ _ hz
  let nc := storage.count+storage.cells cf
  have hclear := BinaryInterpreterStorage.clear_all storage cf
  change (BinaryInterpreterStorage.advance storage nc (BinaryInterpreterStorage.initial storage cf)).cursor.val = 0 ∧
    (∀ i,storage.tapes (BinaryInterpreterStorage.advance storage nc (BinaryInterpreterStorage.initial storage cf)).core i = []) ∧
    BinaryInterpreterStorage.bitSteps storage nc (BinaryInterpreterStorage.initial storage cf) ≤ 3*nc at hclear
  obtain ⟨kc,_,hec,hcc⟩ := forward_clear pf (readDecision cf) (BinaryInterpreterStorage.initial storage cf) nc hclear.1
  let f := {clearingState pf (readDecision cf)
    (BinaryInterpreterStorage.advance storage nc (BinaryInterpreterStorage.initial storage cf)) with phase := .halt}
  have htotal : advance (kl+(ko+(1+kc))) start = f := by
    rw [advance_add,hel,advance_add,heo,advance_add,decision_step,hec]
  refine ⟨kl+(ko+(1+kc)),?_,?_⟩
  · change Finished s lhs rhs code history (advance (kl+(ko+(1+kc))) start)
    rw [htotal]
    exact ⟨rfl,hdecision,hpt,hpcode,hphistory,hpclean,hclear.2.1,hclear.1⟩
  · change bitSteps (kl+(ko+(1+kc))) start ≤ _
    rw [bitSteps_add,hel,bitSteps_add,heo,bitSteps_add,decision_step,decision_cost]
    have hg := core_cells_growth nm c
    change storage.cells cf ≤ storage.cells c+layout.bitSteps nm c at hg
    have hi := encoded_initial_cells storage (lhs.read s) (rhs.read s)
    change storage.cells c ≤ _ at hi
    have hcount := arithmeticStorage_count RationalOp.le
    change storage.count ≤ 96 at hcount
    have hnc : nc = storage.count+storage.cells cf := rfl
    let S := rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hcube : S ≤ S^3 := by
      nlinarith only [Nat.mul_le_mul_left (S*S) hS,Nat.mul_le_mul_left S hS]
    have hsum : rationalEncodingLength (lhs.read s)+rationalEncodingLength (rhs.read s)+1 = S := rfl
    change layout.bitSteps nm c ≤ 5500000*S^3 at hcost
    change _ ≤ 1000*(rationalRegisterEncoding s+s.length+lhs.slots+rhs.slots)+50000000*S^3
    nlinarith only [hnp,hcl,hco,hcc,hclear.2.2,hg,hi,hcount,hnc,hcost,hS,hcube,hsum]

end IdentityTesting.BinaryInterpreterBranchCompare
