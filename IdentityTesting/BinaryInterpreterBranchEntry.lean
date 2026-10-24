import IdentityTesting.BinaryInterpreterBranchRuns
import IdentityTesting.RationalOraclePreparationProgram

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation BinaryRationalRegisters

theorem binary_loopFree_program (pool : BinaryInterpreterPool.Pool)
    (hp : BinaryInterpreterPool.Clean pool) (p : RationalProgram) (hfree : LoopFree p)
    (s : RationalRegisters) (hslots : p.slots ≤ s.length) (code history : List Symbol) :
    ∃ n,
      let start := initial pool (tape s) (RationalProgramCode.program p ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ final.tasks = [] ∧ Result p s code history final.core ∧
      bitSteps n start ≤ cost p s+2 := by
  let core := BinaryInterpreterDispatch.initial pool (tape s) (RationalProgramCode.program p ++ code) history
  let start := initial pool (tape s) (RationalProgramCode.program p ++ code) history
  have hi : BinaryInterpreterDispatch.CleanIO core.io := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨n,f,he,hr,hc⟩ := run_core p hfree s hslots core [] hi hp rfl code rfl
  have hstart : boundary .node (resetTag core) [] = start := rfl
  rw [hstart] at he hc
  have htotal : advance (n+1) start = boundary .halt f [] := by
    rw [advance_add,he]
    rfl
  refine ⟨n+1,?_,?_,?_,?_,?_⟩
  · change (advance (n+1) start).phase = _
    rw [htotal]
    rfl
  · change (advance (n+1) start).frames = _
    rw [htotal]
    rfl
  · change (advance (n+1) start).tasks = _
    rw [htotal]
    rfl
  · change Result p s code history (advance (n+1) start).core
    rw [htotal]
    exact hr
  · change bitSteps (n+1) start ≤ _
    rw [bitSteps_add,he]
    have hlast : bitSteps 1 (boundary .returning f []) = 2 := rfl
    rw [hlast]
    omega

theorem binary_loopFree_program_from_empty (p : RationalProgram) (hfree : LoopFree p)
    (s : RationalRegisters) (hslots : p.slots ≤ s.length) (code history : List Symbol) :
    ∃ n,
      let start := initial BinaryInterpreterPool.empty (tape s) (RationalProgramCode.program p ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ final.tasks = [] ∧ Result p s code history final.core ∧
      bitSteps n start ≤ cost p s+2 :=
  binary_loopFree_program BinaryInterpreterPool.empty BinaryInterpreterPool.empty_clean p hfree s hslots code history

/-- Every arithmetic expression, including nested minimum expressions, now has
an actual code-driven run. The output register and preserved input prefix are
derived from the original expression compiler's proved semantics. -/
theorem binary_expression (e : RationalExpr) (d : ℕ) (s : RationalRegisters)
    (hi : e.inputs ≤ d) (hw : d+e.work ≤ s.length) (code history : List Symbol) :
    ∃ n out,
      let start := initial BinaryInterpreterPool.empty (tape s)
        (RationalProgramCode.program (e.compile d) ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ final.tasks = [] ∧
      final.core.io.tape = tape out ∧ (RationalOperand.reg d).read out = e.eval s ∧
      (∀ i < d, (RationalOperand.reg i).read out = (RationalOperand.reg i).read s) ∧
      BinaryInterpreterDispatch.CleanIO final.core.io ∧ BinaryInterpreterPool.Clean final.core.pool ∧
      final.core.io.code = code ∧ final.core.io.history =
        (RationalProgramCode.program (e.compile d)).reverse ++ history ∧
      bitSteps n start ≤ cost (e.compile d) s+2 := by
  obtain ⟨n,hh,hf,ht,hr,hc⟩ := binary_loopFree_program_from_empty (e.compile d)
    (compile_loopFree e d) s (compile_slots e d s hi hw) code history
  obtain ⟨hout,hprefix⟩ := e.compile_correct d s hi hw
  rcases hr with ⟨hreg,hio,hpool,hcode,hhistory⟩
  exact ⟨n,(e.compile d).exec s,hh,hf,ht,hreg,hout,hprefix,hio,hpool,hcode,hhistory,hc⟩

/-- Actual caller: all seven oracle preparation fields, including pole and
innerRatio, from their original input registers and the specified zero scratch.
Code generation and scratch allocation are not charged by this entry theorem. -/
theorem binary_oracle_field {k : ℕ} (field : OraclePreparationField)
    (a : Fin (k+1) → ℚ) (t σ : ℚ) (code history : List Symbol) :
    ∃ n out,
      let start := initial BinaryInterpreterPool.empty (tape (field.input a t σ))
        (RationalProgramCode.program (field.program k) ++ code) history
      let final := advance n start
      final.phase = .halt ∧ final.frames = [] ∧ final.tasks = [] ∧
      final.core.io.tape = tape out ∧ (RationalOperand.reg (k+3)).read out = field.value a t σ ∧
      (∀ i < k+3, (RationalOperand.reg i).read out = (RationalOperand.reg i).read (field.input a t σ)) ∧
      BinaryInterpreterDispatch.CleanIO final.core.io ∧ BinaryInterpreterPool.Clean final.core.pool ∧
      final.core.io.code = code ∧ final.core.io.history =
        (RationalProgramCode.program (field.program k)).reverse ++ history ∧
      bitSteps n start ≤ cost (field.program k) (field.input a t σ)+2 := by
  have h := binary_expression (field.expression (k+1)) (k+3) (field.input a t σ)
    (field.inputs_le k) (by rw [field.input_length]) code history
  have he : (field.expression (k+1)).eval (field.input a t σ) = field.value a t σ :=
    field.expression_eval a t σ _
  simpa only [OraclePreparationField.program,he] using h

end IdentityTesting.BinaryInterpreterBranchProgram
