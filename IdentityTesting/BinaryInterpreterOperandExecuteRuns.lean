import IdentityTesting.BinaryInterpreterOperandStore

namespace IdentityTesting.BinaryInterpreterOperandExecute
open BinaryInterpreterLayout BinaryInterpreterStorage BinaryRegisterMachine BinaryRationalRegisters RationalComputation
variable {L : Layout} (W : Storage L)

theorem loaded_execution (tape : List Symbol) (dest : List Bool) (code history : List Symbol)
    (p : BinaryInterpreterOperandPair.State L) (h : BinaryInterpreterOperand.Clean p.loader) :
    (dispatch W (loadLift W (initial W tape dest code history) p)).execution =
      BinaryInterpreterArithmeticClean.runningState W
        (BinaryInterpreterArithmetic.operatingState L p.loader.data.core p.loader.tape dest) := by
  rcases h with ⟨ht, ha, hs, hc, hr, hn, hd⟩
  simp [dispatch, loadLift, setPair, initial, BinaryInterpreterArithmeticClean.runningState,
    BinaryInterpreterArithmetic.operatingState, ha, hs, hc, hr, hn, hd]

def Finished (W : Storage L) (s : RationalRegisters) (lhs rhs : RationalOperand) (dst : ℕ) (z : ℚ)
    (code history : List Symbol) (f : State W) : Prop :=
  f.loading = false ∧ f.execution.phase = .halt ∧
  f.execution.core.tape = tape (s.set dst z) ∧
  BinaryInterpreterArithmetic.CleanIO f.execution.core ∧
  (∀ i, W.tapes f.execution.core.core i = []) ∧ f.temp = [] ∧
  f.code = code ∧ f.history =
    (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs).reverse ++ history

/-- A conditional simulation interface; concrete arithmetic correctness is
discharged by actual_local_run in the six-operation theorem. -/
theorem execute_operands (I : InputLocal L) (s : RationalRegisters) (lhs rhs : RationalOperand)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length) (dst : ℕ) (hd : dst < s.length)
    (code history : List Symbol) (nm : ℕ) (z : ℚ)
    (hm : L.halted (L.advance nm (L.initial (BinaryRationalArithmetic.encode (lhs.read s))
      (BinaryRationalArithmetic.encode (rhs.read s)))) = true)
    (hz : L.output (L.advance nm (L.initial (BinaryRationalArithmetic.encode (lhs.read s))
      (BinaryRationalArithmetic.encode (rhs.read s)))) = BinaryRationalArithmetic.encode z) :
    ∃ n,
      let c := L.initial (BinaryRationalArithmetic.encode (lhs.read s)) (BinaryRationalArithmetic.encode (rhs.read s))
      let start := initial W (tape s) (List.replicate dst false)
        (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history
      Finished W s lhs rhs dst z code history (advance W n start) ∧
      bitSteps W n start ≤ 16*L.bitSteps nm c +
        5000*(rationalRegisterEncoding s+s.length+rationalEncodingLength (lhs.read s)+
          rationalEncodingLength (rhs.read s)+lhs.slots+rhs.slots+rationalEncodingLength z+1)+
        6*(W.count+W.cells c) := by
  let source := RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code
  let start := initial W (tape s) (List.replicate dst false) source history
  let p := BinaryInterpreterOperandPair.initial L (tape s) source history
  obtain ⟨np, hnp, hp⟩ := BinaryInterpreterOperandPair.pair_run I s lhs rhs hl hr code history
  let pf := BinaryInterpreterOperandPair.advance np p
  change BinaryInterpreterOperandPair.Loaded s lhs rhs code history pf at hp
  rcases hp with ⟨hph, hpc, hpt, hpcode, hphist, hpclean⟩
  obtain ⟨kl, hkl, hel, hcl⟩ := forward_load W start p np hph
  have hstart : loadLift W start p = start := rfl
  rw [hstart] at hel hcl
  let mid := dispatch W (loadLift W start pf)
  change advance W kl start = mid at hel
  have hmid : mid.execution = BinaryInterpreterArithmeticClean.runningState W
      (BinaryInterpreterArithmetic.operatingState L
        (L.initial (BinaryRationalArithmetic.encode (lhs.read s)) (BinaryRationalArithmetic.encode (rhs.read s)))
        (tape s) (List.replicate dst false)) := by
    rw [loaded_execution W _ _ _ _ pf hpclean, hpc, hpt]
  obtain ⟨ne, heh, het, hei, heclean, hecost⟩ :=
    BinaryInterpreterArithmeticClean.operate_store_clean W s dst hd _ nm z hm hz
  rw [← hmid] at heh het hei heclean hecost
  have hml : mid.loading = false := rfl
  have htotal : advance W (kl+ne) start =
      {mid with execution := BinaryInterpreterArithmeticClean.advance W ne mid.execution} := by
    rw [advance_add, hel, advance_execution W ne mid hml]
  refine ⟨kl+ne, ?_, ?_⟩
  · change Finished W s lhs rhs dst z code history (advance W (kl+ne) start)
    rw [htotal]
    exact ⟨rfl, heh, het, hei, heclean, hpclean.1, hpcode, hphist⟩
  · change bitSteps W (kl+ne) start ≤ _
    rw [bitSteps_add, hel, bitSteps_execution W ne mid hml]
    omega

end IdentityTesting.BinaryInterpreterOperandExecute
