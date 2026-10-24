import IdentityTesting.BinaryInterpreterOperand

namespace IdentityTesting.BinaryInterpreterOperand
open BinaryInterpreterLayout
variable {L : Layout}

def wordLift (frame : State L) (w : BinaryCodeWordLoader.State) : State L :=
  {setWord frame w with phase := .address}
def wordAfter (frame : State L) (w : BinaryCodeWordLoader.State) : State L :=
  {wordLift frame w with phase := .reading}

theorem word_lift_step (right : Bool) (frame : State L) (w : BinaryCodeWordLoader.State)
    (h : w.phase ≠ .halt) :
    step right (wordLift frame w) = wordLift frame (BinaryCodeWordLoader.step w) := by
  simp [step, wordLift, setWord, wordView, h]

theorem word_lift_halt (right : Bool) (frame : State L) (w : BinaryCodeWordLoader.State)
    (h : w.phase = .halt) : step right (wordLift frame w) = wordAfter frame w := by
  simp [step, wordLift, wordAfter, setWord, h]

theorem forward_word (right : Bool) (frame : State L) (w : BinaryCodeWordLoader.State) (n : ℕ)
    (h : (BinaryCodeWordLoader.advance n w).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance right k (wordLift frame w) =
      wordAfter frame (BinaryCodeWordLoader.advance n w) := by
  induction n generalizing w with
  | zero => exact ⟨1, by omega, word_lift_halt right frame w h⟩
  | succ n ih =>
      by_cases hh : w.phase = .halt
      · rw [BinaryCodeLiteralLoader.word_halt (n+1) w hh]
        exact ⟨1, by omega, word_lift_halt right frame w hh⟩
      · obtain ⟨k, hk, he⟩ := ih (BinaryCodeWordLoader.step w) h
        refine ⟨k+1, by omega, ?_⟩
        rw [advance, word_lift_step right frame w hh]
        exact he

def readLift (right : Bool) (frame : State L) (r : BinaryInterpreterRead.State) : State L :=
  {setRead right frame r with phase := .reading}
def readAfter (right : Bool) (frame : State L) (r : BinaryInterpreterRead.State) : State L :=
  {readLift right frame r with phase := .halt}

variable (I : InputLocal L)
include I

theorem read_lift_step (right : Bool) (frame : State L) (r : BinaryInterpreterRead.State)
    (h : r.phase ≠ .halt) :
    step right (readLift right frame r) = readLift right frame (BinaryInterpreterRead.step r) := by
  simp [step, readLift, setRead, readView, I.get_set, I.set_set, h]

omit I in
theorem read_lift_halt (right : Bool) (frame : State L) (r : BinaryInterpreterRead.State)
    (h : r.phase = .halt) : step right (readLift right frame r) = readAfter right frame r := by
  simp [step, readLift, readAfter, setRead, h]

omit I in
theorem read_advance_halt (n : ℕ) (r : BinaryInterpreterRead.State) (h : r.phase = .halt) :
    BinaryInterpreterRead.advance n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryInterpreterRead.advance, BinaryInterpreterRead.step, h] using ih

theorem forward_read (right : Bool) (frame : State L) (r : BinaryInterpreterRead.State) (n : ℕ)
    (h : (BinaryInterpreterRead.advance n r).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance right k (readLift right frame r) =
      readAfter right frame (BinaryInterpreterRead.advance n r) := by
  induction n generalizing r with
  | zero => exact ⟨1, by omega, read_lift_halt right frame r h⟩
  | succ n ih =>
      by_cases hh : r.phase = .halt
      · rw [read_advance_halt (n+1) r hh]
        exact ⟨1, by omega, read_lift_halt right frame r hh⟩
      · obtain ⟨k, hk, he⟩ := ih (BinaryInterpreterRead.step r) h
        refine ⟨k+1, by omega, ?_⟩
        rw [advance, read_lift_step I right frame r hh]
        exact he

def literalLift (right : Bool) (frame : State L) (w : BinaryCodeLiteralLoader.State) : State L :=
  {frame with phase := .literal, data := BinaryInterpreterLiteralInput.lift right frame.data.core w}
def literalAfter (right : Bool) (frame : State L) (w : BinaryCodeLiteralLoader.State) : State L :=
  {literalLift right frame w with phase := .halt}

theorem literal_lift_step (right : Bool) (frame : State L) (w : BinaryCodeLiteralLoader.State)
    (h : w.phase ≠ .halt) :
    step right (literalLift right frame w) = literalLift right frame (BinaryCodeLiteralLoader.step w) := by
  simp only [step, literalLift, BinaryInterpreterLiteralInput.lift]
  simp only [h, if_false]
  exact congrArg (fun d => {frame with phase := .literal, data := d})
    (BinaryInterpreterLiteralInput.step_lift I right frame.data.core w)

omit I in
theorem literal_lift_halt (right : Bool) (frame : State L) (w : BinaryCodeLiteralLoader.State)
    (h : w.phase = .halt) : step right (literalLift right frame w) = literalAfter right frame w := by
  simp [step, literalLift, literalAfter, BinaryInterpreterLiteralInput.lift, h]

omit I in
theorem literal_advance_halt (n : ℕ) (w : BinaryCodeLiteralLoader.State) (h : w.phase = .halt) :
    BinaryCodeLiteralLoader.advance n w = w := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryCodeLiteralLoader.advance, BinaryCodeLiteralLoader.step, h] using ih

theorem forward_literal (right : Bool) (frame : State L) (w : BinaryCodeLiteralLoader.State) (n : ℕ)
    (h : (BinaryCodeLiteralLoader.advance n w).phase = .halt) :
    ∃ k, k ≤ n+1 ∧ advance right k (literalLift right frame w) =
      literalAfter right frame (BinaryCodeLiteralLoader.advance n w) := by
  induction n generalizing w with
  | zero => exact ⟨1, by omega, literal_lift_halt right frame w h⟩
  | succ n ih =>
      by_cases hh : w.phase = .halt
      · rw [literal_advance_halt (n+1) w hh]
        exact ⟨1, by omega, literal_lift_halt right frame w hh⟩
      · obtain ⟨k, hk, he⟩ := ih (BinaryCodeLiteralLoader.step w) h
        refine ⟨k+1, by omega, ?_⟩
        rw [advance, literal_lift_step I right frame w hh]
        exact he

end IdentityTesting.BinaryInterpreterOperand
