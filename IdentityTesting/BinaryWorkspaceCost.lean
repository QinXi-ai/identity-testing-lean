import IdentityTesting.BinaryWorkspaceSignedAdder
import IdentityTesting.BinaryWorkspaceRationalMultiplier

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth

theorem signedMultiplier_step_cells_cost (s : BinarySignedMultiplier.State) :
    signedMultiplierCells (BinarySignedMultiplier.step s) ≤ signedMultiplierCells s + (BinarySignedMultiplier.transitionTrace s).length := by
  have hg := signedMultiplier_step_cells s
  cases hp : s.phase <;> simp only [BinarySignedMultiplier.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinarySignedMultiplier.step, hp] | omega)

theorem signedMultiplier_cells_cost (n : ℕ) (s : BinarySignedMultiplier.State) :
    signedMultiplierCells (BinarySignedMultiplier.advance n s) ≤ signedMultiplierCells s + BinarySignedMultiplier.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinarySignedMultiplier.advance, BinarySignedMultiplier.bitSteps]
  | succ n ih =>
    have hi := ih (BinarySignedMultiplier.step s)
    have hs := signedMultiplier_step_cells_cost s
    simp only [BinarySignedMultiplier.advance, BinarySignedMultiplier.bitSteps]
    omega

theorem signedMultiplier_cleanup_cost (n : ℕ) (s : BinarySignedMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedMultiplierScratch (BinarySignedMultiplier.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (signedMultiplierScratch (BinarySignedMultiplier.advance n s))) ≤
        3 * (11 + signedMultiplierCells s + BinarySignedMultiplier.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := signedMultiplier_cleanup (BinarySignedMultiplier.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := signedMultiplier_cells_cost n s
  omega

theorem signedAdder_step_cells_cost (s : BinarySignedAdder.State) :
    signedAdderCells (BinarySignedAdder.step s) ≤ signedAdderCells s + (BinarySignedAdder.transitionTrace s).length := by
  have hg := signedAdder_step_cells s
  cases hp : s.phase <;> simp only [BinarySignedAdder.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinarySignedAdder.step, hp] | omega)

theorem signedAdder_cells_cost (n : ℕ) (s : BinarySignedAdder.State) :
    signedAdderCells (BinarySignedAdder.advance n s) ≤ signedAdderCells s + BinarySignedAdder.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinarySignedAdder.advance, BinarySignedAdder.bitSteps]
  | succ n ih =>
    have hi := ih (BinarySignedAdder.step s)
    have hs := signedAdder_step_cells_cost s
    simp only [BinarySignedAdder.advance, BinarySignedAdder.bitSteps]
    omega

theorem signedAdder_cleanup_cost (n : ℕ) (s : BinarySignedAdder.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (signedAdderScratch (BinarySignedAdder.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (signedAdderScratch (BinarySignedAdder.advance n s))) ≤
        3 * (11 + signedAdderCells s + BinarySignedAdder.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := signedAdder_cleanup (BinarySignedAdder.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := signedAdder_cells_cost n s
  omega

theorem rationalNormalization_step_cells_cost (s : BinaryRationalNormalizationMachine.State) :
    rationalNormalizationCells (BinaryRationalNormalizationMachine.step s) ≤ rationalNormalizationCells s + (BinaryRationalNormalizationMachine.transitionTrace s).length := by
  have hg := rationalNormalization_step_cells s
  cases hp : s.phase <;> simp only [BinaryRationalNormalizationMachine.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinaryRationalNormalizationMachine.step, hp] | omega)

theorem rationalNormalization_cells_cost (n : ℕ) (s : BinaryRationalNormalizationMachine.State) :
    rationalNormalizationCells (BinaryRationalNormalizationMachine.advance n s) ≤ rationalNormalizationCells s + BinaryRationalNormalizationMachine.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalNormalizationMachine.advance, BinaryRationalNormalizationMachine.bitSteps]
  | succ n ih =>
    have hi := ih (BinaryRationalNormalizationMachine.step s)
    have hs := rationalNormalization_step_cells_cost s
    simp only [BinaryRationalNormalizationMachine.advance, BinaryRationalNormalizationMachine.bitSteps]
    omega

theorem rationalNormalization_cleanup_cost (n : ℕ) (s : BinaryRationalNormalizationMachine.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch (BinaryRationalNormalizationMachine.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch (BinaryRationalNormalizationMachine.advance n s))) ≤
        3 * (42 + rationalNormalizationCells s + BinaryRationalNormalizationMachine.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := rationalNormalization_cleanup (BinaryRationalNormalizationMachine.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalNormalization_cells_cost n s
  omega

theorem rationalMultiplier_step_cells_cost (s : BinaryRationalArithmeticMultiplier.State) :
    rationalMultiplierCells (BinaryRationalArithmeticMultiplier.step s) ≤ rationalMultiplierCells s + (BinaryRationalArithmeticMultiplier.transitionTrace s).length := by
  have hg := rationalMultiplier_step_cells s
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticMultiplier.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinaryRationalArithmeticMultiplier.step, hp] | omega)

theorem rationalMultiplier_cells_cost (n : ℕ) (s : BinaryRationalArithmeticMultiplier.State) :
    rationalMultiplierCells (BinaryRationalArithmeticMultiplier.advance n s) ≤ rationalMultiplierCells s + BinaryRationalArithmeticMultiplier.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticMultiplier.advance, BinaryRationalArithmeticMultiplier.bitSteps]
  | succ n ih =>
    have hi := ih (BinaryRationalArithmeticMultiplier.step s)
    have hs := rationalMultiplier_step_cells_cost s
    simp only [BinaryRationalArithmeticMultiplier.advance, BinaryRationalArithmeticMultiplier.bitSteps]
    omega

theorem rationalMultiplier_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch (BinaryRationalArithmeticMultiplier.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch (BinaryRationalArithmeticMultiplier.advance n s))) ≤
        3 * (67 + rationalMultiplierCells s + BinaryRationalArithmeticMultiplier.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := rationalMultiplier_cleanup (BinaryRationalArithmeticMultiplier.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalMultiplier_cells_cost n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
