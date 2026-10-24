import IdentityTesting.RationalProgramTapeCode

/-! The checkpoint marker does not occur in serialized program code. -/
namespace IdentityTesting.RationalComputation.RationalProgramCode
open BinaryRegisterMachine

theorem word_no_marker (bits : List Bool) : Symbol.cell .component ∉ word bits := by
  simp [word]

theorem tag_no_marker (a b c : Bool) : Symbol.cell .component ∉ tag a b c :=
  word_no_marker _

theorem address_no_marker (i : ℕ) : Symbol.cell .component ∉ address i :=
  word_no_marker _

theorem operand_no_marker (o : RationalOperand) : Symbol.cell .component ∉ operand o := by
  cases o <;> simp only [operand, List.mem_append, not_or, word_no_marker, address_no_marker, and_self, not_false_eq_true]

theorem instruction_no_marker (i : RationalInstruction) : Symbol.cell .component ∉ instruction i := by
  simp only [instruction, List.mem_append, not_or, word_no_marker, address_no_marker, operand_no_marker, and_self, not_false_eq_true]

theorem program_no_marker (p : RationalProgram) : Symbol.cell .component ∉ program p := by
  induction p <;>
    simp_all only [program, List.mem_append, not_or, tag_no_marker, endTag,
      word_no_marker, operand_no_marker, instruction_no_marker, and_self, not_false_eq_true]

theorem control_no_marker (p : RationalControlProgram) : Symbol.cell .component ∉ control p := by
  induction p <;>
    simp_all only [control, List.mem_append, not_or, tag_no_marker, endTag,
      word_no_marker, address_no_marker, operand_no_marker, program_no_marker, and_self, not_false_eq_true]

end IdentityTesting.RationalComputation.RationalProgramCode
