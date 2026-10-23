import IdentityTesting.BinaryWorkspaceCleanup
import IdentityTesting.BinaryMultiplierMachine
import IdentityTesting.BinaryWordNormalization

namespace IdentityTesting.BinaryWorkspaceGrowth

def adderCells (s : BinaryAdderMachine.State) : ℕ :=
  s.left.length + s.right.length + s.work.length + s.out.length

theorem adder_step_cells (s : BinaryAdderMachine.State) :
    adderCells (BinaryAdderMachine.step s) ≤ adderCells s + 1 := by
  cases hp : s.phase <;> simp only [BinaryAdderMachine.step, hp]
  all_goals (repeat' first | split | simp_all [adderCells] | omega)

def normalizerCells (s : BinaryWordNormalization.State) : ℕ :=
  s.source.length + s.work.length + s.out.length

theorem prependNormalized_length (b : Bool) (xs : List Bool) :
    (BinaryWordNormalization.prependNormalized b xs).length ≤ xs.length + 1 := by
  cases xs <;> cases b <;> simp [BinaryWordNormalization.prependNormalized]

theorem normalizer_step_cells (s : BinaryWordNormalization.State) :
    normalizerCells (BinaryWordNormalization.step s) ≤ normalizerCells s := by
  cases hp : s.phase <;> simp only [BinaryWordNormalization.step, hp]
  · split <;> simp_all [normalizerCells] <;> omega
  · cases hw : s.work with
    | nil => simp [normalizerCells]
    | cons b bs =>
      have h := prependNormalized_length b s.out
      simp only [normalizerCells, hw, List.length_cons]
      omega
  · exact le_rfl

def multiplierCells (s : BinaryMultiplierMachine.State) : ℕ :=
  s.factor.length + s.shifted.length + s.temp.length + s.acc.length + adderCells s.adder

theorem multiplier_step_cells (s : BinaryMultiplierMachine.State) :
    multiplierCells (BinaryMultiplierMachine.step s) ≤ multiplierCells s + 1 := by
  have ha := adder_step_cells s.adder
  cases hp : s.phase <;> simp only [BinaryMultiplierMachine.step, hp]
  all_goals (repeat' first | split | simp_all [multiplierCells, adderCells] | omega)

theorem adder_advance_cells (n : ℕ) (s : BinaryAdderMachine.State) :
    adderCells (BinaryAdderMachine.advance n s) ≤ adderCells s + n := by
  induction n generalizing s with
  | zero => simp [BinaryAdderMachine.advance]
  | succ n ih =>
    have hi := ih (BinaryAdderMachine.step s)
    have hs := adder_step_cells s
    simp only [BinaryAdderMachine.advance]
    omega

theorem multiplier_advance_cells (n : ℕ) (s : BinaryMultiplierMachine.State) :
    multiplierCells (BinaryMultiplierMachine.advance n s) ≤ multiplierCells s + n := by
  induction n generalizing s with
  | zero => simp [BinaryMultiplierMachine.advance]
  | succ n ih =>
    have hi := ih (BinaryMultiplierMachine.step s)
    have hs := multiplier_step_cells s
    simp only [BinaryMultiplierMachine.advance]
    omega

end IdentityTesting.BinaryWorkspaceGrowth
