import IdentityTesting.BinaryWorkspaceDivisionGrowth
import IdentityTesting.BinarySignedAdder

namespace IdentityTesting.BinaryWorkspaceGrowth

def signedComparisonCells (s : BinarySignedComparison.State) : ℕ := s.left.length + s.right.length

theorem signedComparison_step_cells (s : BinarySignedComparison.State) :
    signedComparisonCells (BinarySignedComparison.step s) ≤ signedComparisonCells s := by
  cases hp : s.phase <;> simp only [BinarySignedComparison.step, hp]
  · split
    · exact le_rfl
    · simp [signedComparisonCells, BinarySignedComparison.update]
      omega
  all_goals exact le_rfl

def signedAdderCells (s : BinarySignedAdder.State) : ℕ :=
  s.left.length + s.right.length + s.temp.length + signedComparisonCells s.compare +
    adderCells s.arith + normalizerCells s.norm

theorem signedAdder_step_cells (s : BinarySignedAdder.State) :
    signedAdderCells (BinarySignedAdder.step s) ≤ signedAdderCells s + 1 := by
  have hc := signedComparison_step_cells s.compare
  have ha := adder_step_cells s.arith
  have hs := subtractor_step_cells s.arith
  have hn := normalizer_step_cells s.norm
  cases hp : s.phase <;> simp only [BinarySignedAdder.step, hp]
  all_goals (repeat' first | split | simp_all [signedAdderCells, signedComparisonCells,
    adderCells, normalizerCells] | omega)

theorem signedAdder_advance_cells (n : ℕ) (s : BinarySignedAdder.State) :
    signedAdderCells (BinarySignedAdder.advance n s) ≤ signedAdderCells s + n := by
  induction n generalizing s with
  | zero => simp [BinarySignedAdder.advance]
  | succ n ih =>
    have hi := ih (BinarySignedAdder.step s)
    have hs := signedAdder_step_cells s
    simp only [BinarySignedAdder.advance]
    omega

end IdentityTesting.BinaryWorkspaceGrowth

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

def signedAdderScratch (s : BinarySignedAdder.State) : Fin 11 → List Bool :=
  ![s.left, s.right, s.temp, s.compare.left, s.compare.right,
    s.arith.left, s.arith.right, s.arith.work, s.arith.out, s.norm.source, s.norm.work]

theorem signedAdderScratch_cells (s : BinarySignedAdder.State) :
    (∑ i, (signedAdderScratch s i).length) + s.norm.out.length = signedAdderCells s := by
  simp [signedAdderScratch, Fin.sum_univ_succ, signedAdderCells,
    signedComparisonCells, adderCells, normalizerCells]
  omega

theorem signedAdder_cleanup (s : BinarySignedAdder.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedAdderScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (signedAdderScratch s)) ≤
        3 * (11 + signedAdderCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (signedAdderScratch s)
  dsimp only at h
  refine ⟨11 + ∑ i, (signedAdderScratch s i).length, h.2.1, ?_⟩
  have hc := signedAdderScratch_cells s
  omega

theorem signedAdder_cleanup_after (n : ℕ) (s : BinarySignedAdder.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedAdderScratch (BinarySignedAdder.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (signedAdderScratch (BinarySignedAdder.advance n s))) ≤
        3 * (11 + signedAdderCells s + n) := by
  obtain ⟨fuel, hc, hb⟩ := signedAdder_cleanup (BinarySignedAdder.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := signedAdder_advance_cells n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
