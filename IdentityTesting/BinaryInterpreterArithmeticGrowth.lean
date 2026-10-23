import IdentityTesting.BinaryInterpreterStorage
import IdentityTesting.BinaryInterpreterArithmetic
import IdentityTesting.BinaryInterpreterMultiplyGrowth

namespace IdentityTesting.BinaryInterpreterArithmetic
open BinaryInterpreterLayout BinaryInterpreterStorage

variable {L : Layout} (W : Storage L)

theorem setReader_cells (s : State L) (right : Bool) (r : BinaryInterpreterRead.State) :
    W.cells (setReader s right r).core+(reader s right).num.length+(reader s right).den.length =
      W.cells s.core+r.num.length+r.den.length := by
  exact W.input_cells right s.core ⟨⟨r.negative,r.num⟩,r.den⟩

theorem setWriter_cells (s : State L) (w : BinaryInterpreterWrite.State) :
    W.cells (setWriter s w).core+(writer s).num.length+(writer s).den.length =
      W.cells s.core+w.num.length+w.den.length := by
  exact W.output_cells s.core w.num w.den

theorem core_step_cost (s : State L) : W.cells (step s).core ≤ W.cells s.core+(transitionTrace s).length := by
  have hl := BinaryInterpreterMultiply.read_output_growth (reader s false)
  have hr := BinaryInterpreterMultiply.read_output_growth (reader s true)
  have hw := BinaryInterpreterMultiply.write_output_growth (writer s)
  have hcl := setReader_cells W s false (BinaryInterpreterRead.step (reader s false))
  have hcr := setReader_cells W s true (BinaryInterpreterRead.step (reader s true))
  have hcw := setWriter_cells W s (BinaryInterpreterWrite.step (writer s))
  have hm := W.step_cells_cost s.core
  cases hp : s.phase <;> simp only [step,transitionTrace,hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem core_advance_cost (n : ℕ) (s : State L) :
    W.cells (advance n s).core ≤ W.cells s.core+bitSteps n s := by
  induction n generalizing s with
  | zero => simp [advance,bitSteps]
  | succ n ih =>
    have hs := core_step_cost W s
    have hi := ih (step s)
    simp only [advance,bitSteps]
    omega

theorem initial_core_cells (tape : List BinaryRegisterMachine.Symbol) (a b d : List Bool) :
    W.cells (initial L tape a b d).core = 0 := W.initial_cells

end IdentityTesting.BinaryInterpreterArithmetic
