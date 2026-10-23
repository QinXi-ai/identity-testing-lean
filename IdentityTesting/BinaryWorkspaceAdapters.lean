import IdentityTesting.BinaryWorkspaceGrowth
import IdentityTesting.BinarySignedMultiplierRuns

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

def signedMultiplierCells (s : BinarySignedMultiplier.State) : ℕ :=
  multiplierCells s.mul + normalizerCells s.norm + s.temp.length

theorem signedMultiplier_step_cells (s : BinarySignedMultiplier.State) :
    signedMultiplierCells (BinarySignedMultiplier.step s) ≤ signedMultiplierCells s + 1 := by
  have hm := multiplier_step_cells s.mul
  have hn := normalizer_step_cells s.norm
  cases hp : s.phase <;> simp only [BinarySignedMultiplier.step, hp]
  all_goals (repeat' first | split | simp_all [signedMultiplierCells, multiplierCells, normalizerCells] | omega)

theorem signedMultiplier_advance_cells (n : ℕ) (s : BinarySignedMultiplier.State) :
    signedMultiplierCells (BinarySignedMultiplier.advance n s) ≤ signedMultiplierCells s + n := by
  induction n generalizing s with
  | zero => simp [BinarySignedMultiplier.advance]
  | succ n ih =>
    have hi := ih (BinarySignedMultiplier.step s)
    have hs := signedMultiplier_step_cells s
    simp only [BinarySignedMultiplier.advance]
    omega

/-- Naming the same eleven physical scratch stacks; the output stack is a frame.
This is a change of state coordinates, not an executable bulk copy. -/
def signedMultiplierScratch (s : BinarySignedMultiplier.State) : Fin 11 → List Bool :=
  ![s.mul.factor, s.mul.shifted, s.mul.temp, s.mul.acc,
    s.mul.adder.left, s.mul.adder.right, s.mul.adder.work, s.mul.adder.out,
    s.norm.source, s.norm.work, s.temp]

theorem signedMultiplierScratch_cells (s : BinarySignedMultiplier.State) :
    (∑ i, (signedMultiplierScratch s i).length) + s.norm.out.length = signedMultiplierCells s := by
  simp [signedMultiplierScratch, Fin.sum_univ_succ, signedMultiplierCells,
    multiplierCells, adderCells, normalizerCells]
  omega

theorem signedMultiplier_cleanup (s : BinarySignedMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedMultiplierScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (signedMultiplierScratch s)) ≤
        3 * (11 + signedMultiplierCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (signedMultiplierScratch s)
  dsimp only at h
  refine ⟨11 + ∑ i, (signedMultiplierScratch s i).length, h.2.1, ?_⟩
  have hc := signedMultiplierScratch_cells s
  omega

theorem signedMultiplier_cleanup_after (n : ℕ) (s : BinarySignedMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedMultiplierScratch (BinarySignedMultiplier.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (signedMultiplierScratch (BinarySignedMultiplier.advance n s))) ≤
        3 * (11 + signedMultiplierCells s + n) := by
  obtain ⟨fuel, hc, hb⟩ := signedMultiplier_cleanup (BinarySignedMultiplier.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := signedMultiplier_advance_cells n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
