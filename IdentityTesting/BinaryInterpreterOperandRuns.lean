import IdentityTesting.BinaryInterpreterOperandLifts

namespace IdentityTesting.BinaryInterpreterOperand
open BinaryInterpreterLayout BinaryRegisterMachine RationalComputation BinaryRationalRegisters
variable {L : Layout}

def prefixHistory (literal : Bool) (history : List Symbol) : List Symbol :=
  .boundary :: .cell (.bit literal) :: history

theorem consume_kind (right literal : Bool) (c : L.Core) (tape code history : List Symbol) :
    advance right 2 (initial c tape (RationalProgramCode.word [literal] ++ code) history) =
      {initial c tape code (prefixHistory literal history) with phase := if literal then .literal else .address} := by
  cases literal <;> rfl

def Loaded (right : Bool) (c : L.Core) (tape code history : List Symbol)
    (w : Word) (s : State L) : Prop :=
  s.phase = .halt ∧ s.data.core = L.setInput right c w ∧ s.tape = tape ∧
    s.data.code = code ∧ s.data.history = history ∧ Clean s

variable (I : InputLocal L)
include I

theorem literal_operand_run (right : Bool) (c : L.Core) (tape code history : List Symbol) (q : ℚ)
    (hc : L.input right c = BinaryInterpreterArithmetic.emptyWord) :
    ∃ n, n ≤ 2 * rationalEncodingLength q + 11 ∧
      Loaded right c tape code ((RationalProgramCode.operand (.literal q)).reverse ++ history)
        (BinaryRationalArithmetic.encode q)
        (advance right n (initial c tape (RationalProgramCode.operand (.literal q) ++ code) history)) := by
  let w := BinaryRationalArithmetic.encode q
  let hist := prefixHistory true history
  let frame := initial c tape code hist
  let r := BinaryCodeLiteralLoader.initial (BinaryCodeLiteralLoader.encode w ++ code) hist
  obtain ⟨nl, hnl, he, _⟩ := BinaryCodeLiteralLoader.binary_literal_load w code hist
  have hh : (BinaryCodeLiteralLoader.advance nl r).phase = .halt := by rw [he]
  obtain ⟨k, hk, hrun⟩ := forward_literal I right frame r nl hh
  have hset : L.setInput right c BinaryInterpreterArithmetic.emptyWord = c := by
    simpa only [hc] using I.set_self right c
  dsimp only [BinaryInterpreterArithmetic.emptyWord] at hset
  have hstart : advance right 2
      (initial c tape (RationalProgramCode.operand (.literal q) ++ code) history) = literalLift right frame r := by
    rw [BinaryCodeMaterialization.literal_encoding, List.append_assoc, consume_kind]
    simp only [literalLift, frame, r, hist, BinaryInterpreterLiteralInput.lift,
      BinaryCodeLiteralLoader.initial, BinaryCodeLiteralLoader.output, initial,
      BinaryInterpreterLiteralInput.initial]
    rw [hset]
    rfl
  have htotal : advance right (2+k)
      (initial c tape (RationalProgramCode.operand (.literal q) ++ code) history) =
      literalAfter right frame (BinaryCodeLiteralLoader.advance nl r) := by
    rw [advance_add, hstart, hrun]
  refine ⟨2+k, ?_, ?_⟩
  · have hw := BinaryRationalArithmetic.encode_length q
    change 1 + w.numerator.magnitude.length + w.denominator.length = rationalEncodingLength q at hw
    omega
  · rw [htotal]
    change Loaded right c tape code _ w (literalAfter right frame (BinaryCodeLiteralLoader.advance nl r))
    rw [show BinaryCodeLiteralLoader.advance nl r = _ from he]
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [literalAfter, literalLift, BinaryInterpreterLiteralInput.lift, frame, hist,
        prefixHistory, BinaryCodeMaterialization.literal_encoding, RationalProgramCode.word,
        List.reverse_append, List.append_assoc, w]
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem register_operand_run (right : Bool) (c : L.Core) (s : RationalRegisters) (a : ℕ)
    (ha : a < s.length) (code history : List Symbol)
    (hc : L.input right c = BinaryInterpreterArithmetic.emptyWord) :
    ∃ n, n ≤ 3 * (tape s).length + 2 * rationalEncodingLength s[a] + 2*a + 15 ∧
      Loaded right c (tape s) code ((RationalProgramCode.operand (.reg a)).reverse ++ history)
        (BinaryRationalArithmetic.encode s[a])
        (advance right n (initial c (tape s) (RationalProgramCode.operand (.reg a) ++ code) history)) := by
  let hist := prefixHistory false history
  let frame := initial c (tape s) code hist
  let addr : BinaryCodeWordLoader.State :=
    ⟨.reading, RationalProgramCode.address a ++ code, hist, [], []⟩
  let af : BinaryCodeWordLoader.State :=
    ⟨.halt, code, (RationalProgramCode.address a).reverse ++ hist, [], List.replicate a false⟩
  have haRun : BinaryCodeWordLoader.advance (2*a+2) addr = af :=
    (BinaryCodeMaterialization.materialize_address a code hist).1
  have hah : (BinaryCodeWordLoader.advance (2*a+2) addr).phase = .halt := by rw [haRun]
  obtain ⟨ka, hka, hra⟩ := forward_word right frame addr (2*a+2) hah
  rw [haRun] at hra
  have hstart : advance right 2
      (initial c (tape s) (RationalProgramCode.operand (.reg a) ++ code) history) = wordLift frame addr := by
    rw [RationalProgramCode.operand, List.append_assoc, consume_kind]
    rfl
  let frameRead := wordAfter frame af
  let r := BinaryInterpreterRead.initial (tape s) (List.replicate a false)
  obtain ⟨nr, hnr, hr⟩ := BinaryInterpreterCopy.load_steps s a ha
  have hrh : (BinaryInterpreterRead.advance nr r).phase = .halt := by rw [hr]; rfl
  obtain ⟨kr, hkr, hrr⟩ := forward_read I right frameRead r nr hrh
  have hset : L.setInput right c BinaryInterpreterArithmetic.emptyWord = c := by
    simpa only [hc] using I.set_self right c
  dsimp only [BinaryInterpreterArithmetic.emptyWord] at hset
  have hread : readLift right frameRead r = frameRead := by
    simp only [readLift, setRead, frameRead, wordAfter, wordLift, setWord, frame, af,
      r, BinaryInterpreterRead.initial, initial, BinaryInterpreterLiteralInput.initial]
    rw [hset]
  rw [hread, hr] at hrr
  have htotal : advance right (2+(ka+kr))
      (initial c (tape s) (RationalProgramCode.operand (.reg a) ++ code) history) =
      readAfter right frameRead (BinaryInterpreterRead.haltState (tape s) (BinaryRationalArithmetic.encode s[a])) := by
    rw [advance_add, hstart, advance_add, hra]
    exact hrr
  refine ⟨2+(ka+kr), by omega, ?_⟩
  rw [htotal]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp [readAfter, readLift, setRead, frameRead, wordAfter, wordLift, setWord, af, hist,
      prefixHistory, RationalProgramCode.operand, RationalProgramCode.word,
      List.reverse_append, List.append_assoc]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end IdentityTesting.BinaryInterpreterOperand
