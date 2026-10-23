import IdentityTesting.BinaryInterpreterMultiply
import IdentityTesting.BinaryWorkspaceCost

namespace IdentityTesting.BinaryInterpreterMultiply
open BinaryWorkspaceAdapters BinaryWorkspaceGrowth

theorem read_output_growth (r : BinaryInterpreterRead.State) :
    (BinaryInterpreterRead.step r).num.length + (BinaryInterpreterRead.step r).den.length ≤
      r.num.length + r.den.length + 1 := by
  have hs : ∀ t : BinaryRationalRecordMachine.State,
      (BinaryRationalRecordMachine.step t).num.length + (BinaryRationalRecordMachine.step t).den.length ≤
        t.num.length+t.den.length+1 := by
    intro t
    cases hp : t.phase <;> simp only [BinaryRationalRecordMachine.step, hp]
    all_goals (repeat' first | split | simp_all | omega)
  have h := hs (BinaryInterpreterRead.splitter r)
  cases hp : r.phase <;> simp only [BinaryInterpreterRead.step, hp]
  all_goals (repeat' first | split | simp_all [BinaryInterpreterRead.setReader,
    BinaryInterpreterRead.setSplitter, BinaryInterpreterRead.splitter] | omega)

theorem write_output_growth (r : BinaryInterpreterWrite.State) :
    (BinaryInterpreterWrite.step r).num.length + (BinaryInterpreterWrite.step r).den.length ≤
      r.num.length + r.den.length := by
  have hs : ∀ t : BinaryRationalRecordJoin.State,
      (BinaryRationalRecordJoin.step t).num.length + (BinaryRationalRecordJoin.step t).den.length ≤
        t.num.length+t.den.length := by
    intro t
    cases hp : t.phase <;> simp only [BinaryRationalRecordJoin.step, hp]
    all_goals (repeat' first | split | simp_all | omega)
  have h := hs (BinaryInterpreterWrite.joiner r)
  cases hp : r.phase <;> simp only [BinaryInterpreterWrite.step, hp]
  all_goals (repeat' first | split | simp_all [BinaryInterpreterWrite.setWriter,
    BinaryInterpreterWrite.setJoiner, BinaryInterpreterWrite.joiner] | omega)

theorem setReader_cells (s : State) (right : Bool) (r : BinaryInterpreterRead.State) :
    rationalMultiplierCells (setReader s right r).core +
      (reader s right).num.length + (reader s right).den.length =
      rationalMultiplierCells s.core+r.num.length+r.den.length := by
  cases right <;>
    simp [setReader, reader, rationalMultiplierCells, signedMultiplierCells, multiplierCells]
  all_goals omega

theorem setWriter_cells (s : State) (w : BinaryInterpreterWrite.State) :
    rationalMultiplierCells (setWriter s w).core +
      (writer s).num.length + (writer s).den.length =
      rationalMultiplierCells s.core+w.num.length+w.den.length := by
  simp [setWriter, writer, rationalMultiplierCells, rationalNormalizationCells, divisionCells,
    normalizerCells]
  omega

theorem core_step_growth (s : State) :
    rationalMultiplierCells (step s).core ≤ rationalMultiplierCells s.core+1 := by
  have hl := read_output_growth (reader s false)
  have hr := read_output_growth (reader s true)
  have hw := write_output_growth (writer s)
  have hcl := setReader_cells s false (BinaryInterpreterRead.step (reader s false))
  have hcr := setReader_cells s true (BinaryInterpreterRead.step (reader s true))
  have hcw := setWriter_cells s (BinaryInterpreterWrite.step (writer s))
  have hm := rationalMultiplier_step_cells s.core
  cases hp : s.phase <;> simp only [step, hp]
  all_goals (repeat' first | split | simp_all | omega)

theorem core_step_cost (s : State) :
    rationalMultiplierCells (step s).core ≤ rationalMultiplierCells s.core+(transitionTrace s).length := by
  have h := core_step_growth s
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [step] | omega)

theorem core_advance_cost (n : ℕ) (s : State) :
    rationalMultiplierCells (advance n s).core ≤ rationalMultiplierCells s.core+bitSteps n s := by
  induction n generalizing s with
  | zero => simp [advance, bitSteps]
  | succ n ih =>
    have hs := core_step_cost s
    have hi := ih (step s)
    simp only [advance, bitSteps]
    omega

theorem initial_core_cells (tape : List BinaryRegisterMachine.Symbol) (a b d : List Bool) :
    rationalMultiplierCells (initial tape a b d).core = 0 := by
  rfl

end IdentityTesting.BinaryInterpreterMultiply
