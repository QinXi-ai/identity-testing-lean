import IdentityTesting.RationalProgramTapeCode
import IdentityTesting.RationalDynamicRepeat

/-! Bounds for the explicit dynamic-control code tape. The tape representation
uses unary address words and binary canonical rational literals. -/
namespace IdentityTesting.RationalComputation

def RationalControlProgram.slots : RationalControlProgram → ℕ
  | .basic p => p.slots
  | .seq p q => max p.slots q.slots
  | .branchLe a b p q => max (max a.slots b.slots) (max p.slots q.slots)
  | .ceilSize i a => max (i + 1) a.slots
  | .repeatRegister i p => max (i + 1) p.slots

def RationalControlProgram.encoding : RationalControlProgram → ℕ
  | .basic p => p.encoding
  | .seq p q => 1 + p.encoding + q.encoding
  | .branchLe a b p q => 1 + a.encoding + b.encoding + p.encoding + q.encoding
  | .ceilSize i a => 2 + i.size + a.encoding
  | .repeatRegister i p => 1 + i.size + p.encoding

theorem RationalProgramCode.control_length_le (p : RationalControlProgram) (B : ℕ) (h : p.slots ≤ B) :
    (control p).length ≤ 30 * (B + 1) * p.encoding := by
  induction p with
  | basic p => exact program_length_le p B h
  | seq p q hp hq =>
    have hp' := hp ((le_max_left _ _).trans h)
    have hq' := hq ((le_max_right _ _).trans h)
    simp only [control, List.length_append, tag_length, endTag, RationalControlProgram.encoding]
    nlinarith
  | branchLe a b p q hp hq =>
    have hab : max a.slots b.slots ≤ B := (le_max_left _ _).trans h
    have hpq : max p.slots q.slots ≤ B := (le_max_right _ _).trans h
    have ha := operand_length_le a B ((le_max_left _ _).trans hab)
    have hb := operand_length_le b B ((le_max_right _ _).trans hab)
    have hp' := hp ((le_max_left _ _).trans hpq)
    have hq' := hq ((le_max_right _ _).trans hpq)
    simp only [control, List.length_append, tag_length, endTag, RationalControlProgram.encoding]
    nlinarith
  | ceilSize i a =>
    have hi : i + 1 ≤ B := (le_max_left _ _).trans h
    have ha := operand_length_le a B ((le_max_right _ _).trans h)
    simp only [control, List.length_append, tag_length, address_length, RationalControlProgram.encoding]
    nlinarith
  | repeatRegister i p hp =>
    have hi : i + 1 ≤ B := (le_max_left _ _).trans h
    have hp' := hp ((le_max_right _ _).trans h)
    simp only [control, List.length_append, tag_length, endTag, address_length, RationalControlProgram.encoding]
    nlinarith

theorem RationalProgram.dynamicRepeats_slots (p : RationalProgram) (i : ℕ) :
    (p.dynamicRepeats i).slots ≤ max p.slots (i + 1) := by
  induction p with
  | skip => exact Nat.zero_le _
  | instr j => exact le_max_left _ _
  | seq p q hp hq =>
    simp only [dynamicRepeats, RationalControlProgram.slots, slots]
    omega
  | branchLe a b p q hp hq =>
    simp only [dynamicRepeats, RationalControlProgram.slots, slots]
    omega
  | «repeat» n p hp =>
    simp only [dynamicRepeats, RationalControlProgram.slots, slots]
    omega

theorem RationalProgram.dynamicRepeats_encoding (p : RationalProgram) (i : ℕ) :
    (p.dynamicRepeats i).encoding ≤ (i.size + 1) * p.encoding := by
  induction p with
  | skip => simp [dynamicRepeats, RationalControlProgram.encoding, encoding]
  | instr j =>
    change (RationalProgram.instr j).encoding ≤ (i.size + 1) * (RationalProgram.instr j).encoding
    nlinarith
  | seq p q hp hq =>
    simp only [dynamicRepeats, RationalControlProgram.encoding, encoding]
    nlinarith
  | branchLe a b p q hp hq =>
    simp only [dynamicRepeats, RationalControlProgram.encoding, encoding]
    nlinarith
  | «repeat» n p hp =>
    simp only [dynamicRepeats, RationalControlProgram.encoding, encoding]
    nlinarith

end IdentityTesting.RationalComputation
