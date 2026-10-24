import IdentityTesting.BinaryInterpreterProgramRuns

/-! Top-level entry for the supported skip/instruction/sequence grammar. The
returning continuation produced by run_core takes one actual controller step
to halt, with an empty continuation stack and two charged trace actions. -/
namespace IdentityTesting.BinaryInterpreterProgram
open BinaryRegisterMachine RationalComputation BinaryRationalRegisters

theorem binary_straight_program (pool : BinaryInterpreterPool.Pool)
    (hp : BinaryInterpreterPool.Clean pool) (p : RationalProgram) (hstraight : Straight p)
    (s : RationalRegisters) (hslots : p.slots ≤ s.length) (code history : List Symbol) :
    ∃ n,
      let start := initial pool (tape s) (RationalProgramCode.program p ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ Result p s code history final.core ∧
      bitSteps n start ≤ cost p s+2 := by
  let core := BinaryInterpreterDispatch.initial pool (tape s) (RationalProgramCode.program p ++ code) history
  let start := initial pool (tape s) (RationalProgramCode.program p ++ code) history
  have hclean : BinaryInterpreterDispatch.CleanIO core.io :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨n,f,he,hr,hc⟩ := run_core p hstraight s hslots core [] hclean hp rfl code rfl
  have hstart : (⟨.node,resetTag core,[]⟩ : State) = start := rfl
  rw [hstart] at he hc
  have htotal : advance (n+1) start = ⟨.halt,f,[]⟩ := by
    rw [advance_add,he]
    rfl
  refine ⟨n+1,?_,?_,?_,?_⟩
  · change (advance (n+1) start).phase = _
    rw [htotal]
  · change (advance (n+1) start).frames = _
    rw [htotal]
  · change Result p s code history (advance (n+1) start).core
    rw [htotal]
    exact hr
  · change bitSteps (n+1) start ≤ _
    rw [bitSteps_add,he]
    have hlast : bitSteps 1 ⟨.returning,f,[]⟩ = 2 := rfl
    rw [hlast]
    omega

/-- No operation, destination or success certificate is supplied to the entry
machine. The source program is present only through its encoded code tape;
Straight states precisely which node constructors this controller implements. -/
theorem binary_straight_program_from_empty (p : RationalProgram) (hstraight : Straight p)
    (s : RationalRegisters) (hslots : p.slots ≤ s.length) (code history : List Symbol) :
    ∃ n,
      let start := initial BinaryInterpreterPool.empty (tape s) (RationalProgramCode.program p ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ Result p s code history final.core ∧
      bitSteps n start ≤ cost p s+2 :=
  binary_straight_program BinaryInterpreterPool.empty BinaryInterpreterPool.empty_clean p hstraight s hslots code history

end IdentityTesting.BinaryInterpreterProgram
