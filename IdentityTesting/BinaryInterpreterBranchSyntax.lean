import IdentityTesting.RationalExpressionBounds
import IdentityTesting.RationalProgramTapeCode

namespace IdentityTesting.BinaryInterpreterBranchProgram
open RationalComputation

/-- The fragment needed by the full rational-expression compiler, including
minimum expressions. Repetition remains a separate controller obligation. -/
def LoopFree : RationalProgram → Prop
  | .skip | .instr _ => True
  | .seq p q | .branchLe _ _ p q => LoopFree p ∧ LoopFree q
  | .repeat _ _ => False

theorem compile_loopFree (e : RationalExpr) (d : ℕ) : LoopFree (e.compile d) := by
  induction e generalizing d with
  | operand o => trivial
  | binary op a b ha hb => exact ⟨ha d,hb (d+1),True.intro⟩
  | minimum a b ha hb => exact ⟨ha d,hb (d+1),True.intro,True.intro⟩

theorem compile_slots (e : RationalExpr) (d : ℕ) (s : RationalRegisters)
    (hi : e.inputs ≤ d) (hw : d+e.work ≤ s.length) : (e.compile d).slots ≤ s.length := by
  have h := e.compile_slots d
  omega

end IdentityTesting.BinaryInterpreterBranchProgram
