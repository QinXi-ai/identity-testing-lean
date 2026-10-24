import IdentityTesting.RationalDynamicControl
import IdentityTesting.BinaryRegisterMachine

/-! Explicit code tapes over the existing four-symbol register-machine alphabet.
Every word has a boundary. Addresses are unary, rational literals use canonical
binary numerator/denominator words. Compound nodes have an explicit end tag.
These definitions specify the tape to generate; generation is not a free
machine operation and must be implemented separately. -/
namespace IdentityTesting.RationalComputation
namespace RationalProgramCode

open BinaryRegisterMachine

def word (bits : List Bool) : List Symbol :=
  bits.map (fun b => Symbol.cell (.bit b)) ++ [.boundary]

def tag (a b c : Bool) : List Symbol := word [a, b, c]

def address (i : ℕ) : List Symbol := word (List.replicate i false)

def opBits : RationalOp → List Bool
  | .copy => [false, false, false]
  | .add => [true, false, false]
  | .sub => [false, true, false]
  | .mul => [true, true, false]
  | .div => [false, false, true]
  | .le => [true, false, true]

def operand : RationalOperand → List Symbol
  | .reg i => word [false] ++ address i
  | .literal q => word [true] ++ word [decide (q.num < 0)] ++
      word q.num.natAbs.bits ++ word q.den.bits

def instruction (i : RationalInstruction) : List Symbol :=
  word (opBits i.op) ++ address i.dst ++ operand i.lhs ++ operand i.rhs

def endTag : List Symbol := tag true true true

def program : RationalProgram → List Symbol
  | .skip => tag false false false
  | .instr i => tag true false false ++ instruction i
  | .seq p q => tag false true false ++ program p ++ program q ++ endTag
  | .branchLe a b p q => tag true true false ++ operand a ++ operand b ++ program p ++ program q ++ endTag
  | .repeat n p => tag false false true ++ word n.bits ++ program p ++ endTag

def control : RationalControlProgram → List Symbol
  | .basic p => program p
  | .seq p q => tag false true false ++ control p ++ control q ++ endTag
  | .branchLe a b p q => tag true true false ++ operand a ++ operand b ++ control p ++ control q ++ endTag
  | .ceilSize i a => tag true false true ++ address i ++ operand a
  | .repeatRegister i p => tag false true true ++ address i ++ control p ++ endTag

theorem word_length (bits : List Bool) : (word bits).length = bits.length + 1 := by
  simp [word]

theorem tag_length (a b c : Bool) : (tag a b c).length = 4 := rfl

theorem address_length (i : ℕ) : (address i).length = i + 1 := by
  simp [address, word_length]

theorem operand_length_le (o : RationalOperand) (B : ℕ) (h : o.slots ≤ B) :
    (operand o).length ≤ (B + 5) * o.encoding := by
  cases o with
  | reg i =>
    simp only [RationalOperand.slots] at h
    simp only [operand, List.length_append, word_length, List.length_cons, List.length_nil,
      address_length, RationalOperand.encoding]
    nlinarith
  | literal q =>
    simp only [operand, List.length_append, word_length, List.length_cons, List.length_nil,
      ← Nat.size_eq_bits_len, RationalOperand.encoding, rationalEncodingLength, numeratorBits, denominatorBits]
    nlinarith

theorem instruction_length_le (i : RationalInstruction) (B : ℕ)
    (h : (RationalProgram.instr i).slots ≤ B) :
    (instruction i).length ≤ 10 * (B + 1) * (2 + i.dst.size + i.lhs.encoding + i.rhs.encoding) := by
  have hd : i.dst + 1 ≤ B := (le_max_left _ _).trans h
  have hl := operand_length_le i.lhs B ((le_max_left _ _).trans ((le_max_right _ _).trans h))
  have hr := operand_length_le i.rhs B ((le_max_right _ _).trans ((le_max_right _ _).trans h))
  have hop : (opBits i.op).length = 3 := by cases i.op <;> rfl
  simp only [instruction, List.length_append, word_length, hop, address_length]
  nlinarith

theorem program_length_le (p : RationalProgram) (B : ℕ) (h : p.slots ≤ B) :
    (program p).length ≤ 30 * (B + 1) * p.encoding := by
  induction p with
  | skip => simp [program, tag_length, RationalProgram.encoding]; omega
  | instr i =>
    have hi := instruction_length_le i B h
    simp only [program, List.length_append, tag_length, RationalProgram.encoding]
    nlinarith
  | seq p q hp hq =>
    have hp' := hp ((le_max_left _ _).trans h)
    have hq' := hq ((le_max_right _ _).trans h)
    simp only [program, List.length_append, tag_length, endTag, RationalProgram.encoding]
    nlinarith
  | branchLe a b p q hp hq =>
    have hab : max a.slots b.slots ≤ B := (le_max_left _ _).trans h
    have hpq : max p.slots q.slots ≤ B := (le_max_right _ _).trans h
    have ha := operand_length_le a B ((le_max_left _ _).trans hab)
    have hb := operand_length_le b B ((le_max_right _ _).trans hab)
    have hp' := hp ((le_max_left _ _).trans hpq)
    have hq' := hq ((le_max_right _ _).trans hpq)
    simp only [program, List.length_append, tag_length, endTag, RationalProgram.encoding]
    nlinarith
  | «repeat» n p hp =>
    have hp' := hp h
    simp only [program, List.length_append, tag_length, word_length, ← Nat.size_eq_bits_len, endTag,
      RationalProgram.encoding]
    nlinarith

end RationalProgramCode
end IdentityTesting.RationalComputation
