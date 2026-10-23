import IdentityTesting.BinaryInterpreterLayout

namespace IdentityTesting.BinaryInterpreterLayouts
open BinaryInterpreterLayout

/-- Both words are physical input stacks. The copy result aliases the left
input; no transition duplicates it. The shared loader has already copied the
source register, and the shared writer subsequently consumes these stacks. -/
structure CopyCore where
  halted : Bool
  left : Word
  right : Word

def copyStep (c : CopyCore) : CopyCore := {c with halted := true}
def copyTrace (c : CopyCore) : List BinaryArithmetic.BitOp := if c.halted then [] else [.branch]
def copyInput (right : Bool) (c : CopyCore) : Word := if right then c.right else c.left
def copySetInput (right : Bool) (c : CopyCore) (w : Word) : CopyCore :=
  if right then {c with right := w} else {c with left := w}
def copySetOutput (c : CopyCore) (n d : List Bool) : CopyCore :=
  {c with left := ⟨⟨c.left.numerator.negative,n⟩,d⟩}

def copying : Layout where
  Core := CopyCore
  initial := fun x y => ⟨false,x,y⟩
  step := copyStep
  halted := CopyCore.halted
  trace := copyTrace
  input := copyInput
  setInput := copySetInput
  output := CopyCore.left
  setOutput := copySetOutput
  input_initial := by intro right x y; cases right <;> rfl
  setInput_initial := by intro right x y w; cases right <;> rfl
  output_num_set := by intros; rfl
  output_den_set := by intros; rfl
  setOutput_self := by intros; rfl
  setOutput_set := by intros; rfl
  step_halt := by intro c h; cases c; simp_all [copyStep]
  trace_active := by intro c h; simp [copyTrace,h]
  trace_bound := by intro c; unfold copyTrace; split <;> simp

theorem copying_run (x y : Word) :
    copying.halted (copying.advance 1 (copying.initial x y)) = true ∧
    copying.output (copying.advance 1 (copying.initial x y)) = x ∧
    copying.bitSteps 1 (copying.initial x y) = 1 := by
  exact ⟨rfl,rfl,rfl⟩

end IdentityTesting.BinaryInterpreterLayouts
