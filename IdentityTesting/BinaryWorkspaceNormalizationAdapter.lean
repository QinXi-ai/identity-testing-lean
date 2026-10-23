import IdentityTesting.BinaryWorkspaceDivisionGrowth

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

/-- The 42 non-output physical stacks of the rational normalization machine. -/
def rationalNormalizationScratch (s : BinaryRationalNormalizationMachine.State) : Fin 42 → List Bool :=
  ![s.gcd.div.source, s.gcd.div.bits, s.gcd.div.divisor, s.gcd.div.temp,
    s.gcd.div.sub.left, s.gcd.div.sub.right, s.gcd.div.sub.work, s.gcd.div.sub.out,
    s.gcd.div.quot.source, s.gcd.div.quot.work, s.gcd.div.quot.out,
    s.gcd.div.rem.source, s.gcd.div.rem.work, s.gcd.div.rem.out, s.gcd.temp,
    s.num.source, s.num.bits, s.num.divisor, s.num.temp,
    s.num.sub.left, s.num.sub.right, s.num.sub.work, s.num.sub.out,
    s.num.quot.source, s.num.quot.work,
    s.num.rem.source, s.num.rem.work, s.num.rem.out,
    s.den.source, s.den.bits, s.den.divisor, s.den.temp,
    s.den.sub.left, s.den.sub.right, s.den.sub.work, s.den.sub.out,
    s.den.quot.source, s.den.quot.work,
    s.den.rem.source, s.den.rem.work, s.den.rem.out, s.temp]

theorem rationalNormalizationScratch_cells (s : BinaryRationalNormalizationMachine.State) :
    (∑ i, (rationalNormalizationScratch s i).length) + s.num.quot.out.length + s.den.quot.out.length =
      rationalNormalizationCells s := by
  simp [rationalNormalizationScratch, Fin.sum_univ_succ, rationalNormalizationCells,
    gcdCells, divisionCells, adderCells, normalizerCells]
  omega

theorem rationalNormalization_cleanup (s : BinaryRationalNormalizationMachine.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch s)) ≤
        3 * (42 + rationalNormalizationCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalNormalizationScratch s)
  dsimp only at h
  refine ⟨42 + ∑ i, (rationalNormalizationScratch s i).length, h.2.1, ?_⟩
  have hc := rationalNormalizationScratch_cells s
  omega

theorem rationalNormalization_cleanup_after (n : ℕ) (s : BinaryRationalNormalizationMachine.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch (BinaryRationalNormalizationMachine.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalNormalizationScratch (BinaryRationalNormalizationMachine.advance n s))) ≤
        3 * (42 + rationalNormalizationCells s + n) := by
  obtain ⟨fuel, hc, hb⟩ := rationalNormalization_cleanup (BinaryRationalNormalizationMachine.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalNormalization_advance_cells n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
