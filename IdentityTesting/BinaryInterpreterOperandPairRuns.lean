import IdentityTesting.BinaryInterpreterOperandPair

namespace IdentityTesting.BinaryInterpreterOperandPair
open BinaryInterpreterLayout BinaryRegisterMachine RationalComputation BinaryRationalRegisters
variable {L : Layout}

def Loaded (s : RationalRegisters) (lhs rhs : RationalOperand)
    (code history : List Symbol) (f : State L) : Prop :=
  f.phase = .halt ∧
  f.loader.data.core = L.initial (BinaryRationalArithmetic.encode (lhs.read s))
    (BinaryRationalArithmetic.encode (rhs.read s)) ∧
  f.loader.tape = tape s ∧ f.loader.data.code = code ∧
  f.loader.data.history = (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs).reverse ++ history ∧
  BinaryInterpreterOperand.Clean f.loader

/-- Both operand discriminators and payloads are consumed by the same loader.
The only operand validity premises bound register addresses. -/
theorem pair_run (I : InputLocal L) (s : RationalRegisters) (lhs rhs : RationalOperand)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length)
    (code history : List Symbol) :
    ∃ n, n ≤ 50 * (rationalRegisterEncoding s + s.length +
      rationalEncodingLength (lhs.read s) + rationalEncodingLength (rhs.read s) + lhs.slots + rhs.slots + 1) ∧
      Loaded s lhs rhs code history
        (advance n (initial L (tape s)
          (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history)) := by
  let c := L.initial BinaryInterpreterArithmetic.emptyWord BinaryInterpreterArithmetic.emptyWord
  have hc : L.input false c = BinaryInterpreterArithmetic.emptyWord := by simp [c, L.input_initial]
  obtain ⟨nl, hnl, hleft⟩ := BinaryInterpreterOperand.operand_run I false c s lhs hl
    (RationalProgramCode.operand rhs ++ code) history hc
  let start := BinaryInterpreterOperand.initial c (tape s)
    (RationalProgramCode.operand lhs ++ (RationalProgramCode.operand rhs ++ code)) history
  let fl := BinaryInterpreterOperand.advance false nl start
  change BinaryInterpreterOperand.Loaded false c (tape s) _ _ _ fl at hleft
  rcases hleft with ⟨hlhalt, hlcore, hltape, hlcode, hlhist, hlclean⟩
  have hrc : L.input true fl.data.core = BinaryInterpreterArithmetic.emptyWord := by
    rw [hlcore]
    simpa [c, L.input_initial] using I.other false c (BinaryRationalArithmetic.encode (lhs.read s))
  obtain ⟨nr, hnr, hright⟩ := BinaryInterpreterOperand.operand_run I true fl.data.core s rhs hr
    code ((RationalProgramCode.operand lhs).reverse ++ history) hrc
  let sr := BinaryInterpreterOperand.initial fl.data.core (tape s)
    (RationalProgramCode.operand rhs ++ code) ((RationalProgramCode.operand lhs).reverse ++ history)
  let fr := BinaryInterpreterOperand.advance true nr sr
  change BinaryInterpreterOperand.Loaded true fl.data.core (tape s) _ _ _ fr at hright
  rcases hright with ⟨hrhalt, hrcore, hrtape, hrcode, hrhist, hrclean⟩
  obtain ⟨kl, hkl, hel⟩ := forward false start nl hlhalt
  obtain ⟨kr, hkr, her⟩ := forward true sr nr hrhalt
  have hrearm : BinaryInterpreterOperand.rearm fl = sr := by
    rw [BinaryInterpreterOperand.rearm_clean fl hlclean, hltape, hlcode, hlhist]
  have hmid : after false fl = lift true sr := by simp only [after, Bool.false_eq_true, if_false, lift, if_true, hrearm]
  have hstart : initial L (tape s)
      (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history = lift false start := by
    simp only [initial, lift, Bool.false_eq_true, if_false, start, c, List.append_assoc]
  have htotal : advance (kl+kr) (initial L (tape s)
      (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history) = after true fr := by
    rw [advance_add, hstart, hel, hmid, her]
  refine ⟨kl+kr, by omega, ?_⟩
  rw [htotal]
  refine ⟨rfl, ?_, hrtape, hrcode, ?_, hrclean⟩
  · change fr.data.core = _
    rw [hrcore, hlcore]
    simp only [c, L.setInput_initial, Bool.false_eq_true, if_false, if_true]
  · change fr.data.history = _
    rw [hrhist]
    simp only [List.reverse_append, List.append_assoc]

theorem pair_load (I : InputLocal L) (s : RationalRegisters) (lhs rhs : RationalOperand)
    (hl : lhs.slots ≤ s.length) (hr : rhs.slots ≤ s.length)
    (code history : List Symbol) :
    ∃ n,
      let start := initial L (tape s)
        (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history
      Loaded s lhs rhs code history (advance n start) ∧
      bitSteps n start ≤ 800 * (rationalRegisterEncoding s + s.length +
        rationalEncodingLength (lhs.read s) + rationalEncodingLength (rhs.read s) + lhs.slots + rhs.slots + 1) := by
  obtain ⟨n, hn, hrun⟩ := pair_run I s lhs rhs hl hr code history
  refine ⟨n, hrun, ?_⟩
  have hb := bitSteps_le n (initial L (tape s)
    (RationalProgramCode.operand lhs ++ RationalProgramCode.operand rhs ++ code) history)
  omega

end IdentityTesting.BinaryInterpreterOperandPair
