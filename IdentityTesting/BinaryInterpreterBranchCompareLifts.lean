import IdentityTesting.BinaryInterpreterBranchCompare

namespace IdentityTesting.BinaryInterpreterBranchCompare
open BinaryInterpreterLayout BinaryInterpreterStorage RationalComputation

theorem halt_step (s : State) (h : s.phase = .halt) : step s = s := by simp [step,h]
theorem halt_advance (n : ℕ) (s : State) (h : s.phase = .halt) : advance n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [advance,halt_step s h] using ih
theorem trace_active (s : State) (h : s.phase ≠ .halt) : 1 ≤ (transitionTrace s).length := by
  cases hp:s.phase <;> simp_all only [transitionTrace]
  all_goals (repeat' first | split | simp_all)

theorem forward_load (p : Pair) (n : ℕ) (h : (BinaryInterpreterOperandPair.advance n p).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance k (loadingState p) =
      operatingState (BinaryInterpreterOperandPair.advance n p) (pairCore (BinaryInterpreterOperandPair.advance n p)) ∧
      bitSteps k (loadingState p) ≤ 17*n+1 := by
  induction n generalizing p with
  | zero =>
    change p.phase = .halt at h
    refine ⟨1,by omega,?_,?_⟩
    · cases p
      simp_all [advance,step,loadingState,operatingState,BinaryInterpreterOperandPair.advance,setPairCore,pairCore]
    · simp [bitSteps,transitionTrace,loadingState,h]
  | succ n ih =>
    by_cases hh : p.phase = .halt
    · rw [BinaryInterpreterOperandExecute.pair_halt (n+1) p hh]
      refine ⟨1,by omega,?_,?_⟩
      · cases p
        simp_all [advance,step,loadingState,operatingState,setPairCore,pairCore]
      · simp [bitSteps,transitionTrace,loadingState,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterOperandPair.step p) h
      refine ⟨k+1,by omega,?_,?_⟩
      · simpa [advance,step,loadingState,hh] using he
      · have ht := BinaryInterpreterOperandPair.transition_length p
        simp only [bitSteps,transitionTrace,loadingState,step,if_neg hh,List.length_cons]
        change (BinaryInterpreterOperandPair.transitionTrace p).length+1+
          bitSteps k (loadingState (BinaryInterpreterOperandPair.step p)) ≤ _
        omega

theorem operate_step (p : Pair) (c : Core) (h : layout.halted c ≠ true) :
    step (operatingState p c) = operatingState p (layout.step c) := by
  simp [step,operatingState,core,pairCore,setCore,setPairCore,h]
theorem operate_halt (p : Pair) (c : Core) (h : layout.halted c = true) :
    step (operatingState p c) = decisionState p c := by
  simp [step,operatingState,decisionState,core,pairCore,setPairCore,h]

theorem forward_operate (p : Pair) (c : Core) (n : ℕ) (h : layout.halted (layout.advance n c) = true) :
    ∃ k, k ≤ n+1 ∧ advance k (operatingState p c) = decisionState p (layout.advance n c) ∧
      bitSteps k (operatingState p c) ≤ 2*layout.bitSteps n c+1 := by
  induction n generalizing c with
  | zero =>
    change layout.halted c = true at h
    refine ⟨1,by omega,operate_halt p c h,?_⟩
    simp [bitSteps,transitionTrace,operatingState,core,pairCore,setPairCore,h,Layout.bitSteps]
  | succ n ih =>
    by_cases hh : layout.halted c = true
    · rw [layout.advance_halt (n+1) c hh]
      refine ⟨1,by omega,operate_halt p c hh,?_⟩
      simp [bitSteps,transitionTrace,operatingState,core,pairCore,setPairCore,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (layout.step c) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,operate_step p c hh]
        exact he
      · have ht := layout.trace_active c hh
        rw [bitSteps,operate_step p c hh]
        change (if layout.halted c = true then [BinaryArithmetic.BitOp.branch] else
          BinaryArithmetic.BitOp.branch :: layout.trace c).length +
          bitSteps k (operatingState p (layout.step c)) ≤ _
        simp only [if_neg hh,List.length_cons,Layout.bitSteps]
        omega

theorem decision_step (p : Pair) (c : Core) :
    advance 1 (decisionState p c) = clearingState p (readDecision c) (BinaryInterpreterStorage.initial storage c) := rfl
theorem decision_cost (p : Pair) (c : Core) : bitSteps 1 (decisionState p c) = 2 := rfl

theorem clear_step (p : Pair) (d : Bool) (w : BinaryInterpreterStorage.State storage) (h : w.cursor.val ≠ 0) :
    step (clearingState p d w) = clearingState p d (BinaryInterpreterStorage.step storage w) := by
  simp [step,clearingState,storageView,core,pairCore,setPairCore,setStorage,setCore,h]
theorem clear_halt (p : Pair) (d : Bool) (w : BinaryInterpreterStorage.State storage) (h : w.cursor.val = 0) :
    step (clearingState p d w) = {clearingState p d w with phase := .halt} := by
  simp [step,clearingState,h]

theorem forward_clear (p : Pair) (d : Bool) (w : BinaryInterpreterStorage.State storage) (n : ℕ)
    (h : (BinaryInterpreterStorage.advance storage n w).cursor.val = 0) :
    ∃ k, k ≤ n+1 ∧ advance k (clearingState p d w) =
      {clearingState p d (BinaryInterpreterStorage.advance storage n w) with phase := .halt} ∧
      bitSteps k (clearingState p d w) ≤ 2*BinaryInterpreterStorage.bitSteps storage n w+1 := by
  induction n generalizing w with
  | zero =>
    change w.cursor.val = 0 at h
    refine ⟨1,by omega,clear_halt p d w h,?_⟩
    simp [bitSteps,transitionTrace,clearingState,h,BinaryInterpreterStorage.bitSteps]
  | succ n ih =>
    by_cases hh : w.cursor.val = 0
    · rw [BinaryInterpreterArithmeticClean.storage_halt storage (n+1) w hh]
      refine ⟨1,by omega,clear_halt p d w hh,?_⟩
      simp [bitSteps,transitionTrace,clearingState,hh]
    · obtain ⟨k,hk,he,hc⟩ := ih (BinaryInterpreterStorage.step storage w) h
      refine ⟨k+1,by omega,?_,?_⟩
      · rw [advance,clear_step p d w hh]
        exact he
      · have ht : 1 ≤ (BinaryInterpreterStorage.transitionTrace storage w).length := by
          simp only [BinaryInterpreterStorage.transitionTrace,BinaryInterpreterStorage.view,
            BinaryWorkspaceCleanup.transitionTrace,dif_neg hh]
          split <;> simp
        rw [bitSteps,clear_step p d w hh]
        change (if w.cursor.val = 0 then [BinaryArithmetic.BitOp.branch] else
          BinaryArithmetic.BitOp.branch :: BinaryInterpreterStorage.transitionTrace storage w).length +
          bitSteps k (clearingState p d (BinaryInterpreterStorage.step storage w)) ≤ _
        simp only [if_neg hh,List.length_cons,BinaryInterpreterStorage.bitSteps]
        omega

theorem core_cells_growth (n : ℕ) (c : Core) :
    storage.cells (layout.advance n c) ≤ storage.cells c+layout.bitSteps n c := by
  induction n generalizing c with
  | zero => simp [Layout.advance,Layout.bitSteps]
  | succ n ih =>
    have hs := storage.step_cells_cost c
    have hi := ih (layout.step c)
    simp only [Layout.advance,Layout.bitSteps]
    omega

theorem readDecision_of_output (c : Core) (p q : ℚ)
    (h : layout.output c = BinaryRationalArithmetic.encode (RationalOp.le.eval p q)) :
    readDecision c = decide (p ≤ q) := by
  unfold readDecision
  rw [h]
  by_cases hp : p ≤ q <;>
    simp [RationalOp.eval,hp,BinaryRationalArithmetic.encode,BinarySignedWords.encode]

end IdentityTesting.BinaryInterpreterBranchCompare
