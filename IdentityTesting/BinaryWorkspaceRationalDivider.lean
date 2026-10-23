import IdentityTesting.BinaryWorkspaceCost
import IdentityTesting.BinaryRationalArithmeticDivider

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

def rationalDividerCells (s : BinaryRationalArithmeticDivider.State) : ℕ :=
  rationalMultiplierCells s.core + s.zeroDen.length

theorem rationalDivider_step_cells (s : BinaryRationalArithmeticDivider.State) :
    rationalDividerCells (BinaryRationalArithmeticDivider.step s) ≤ rationalDividerCells s + 1 := by
  have hc := rationalMultiplier_step_cells s.core
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticDivider.step, hp]
  all_goals (repeat' first | split | simp_all [rationalDividerCells] | omega)

theorem rationalDivider_step_cells_cost (s : BinaryRationalArithmeticDivider.State) :
    rationalDividerCells (BinaryRationalArithmeticDivider.step s) ≤ rationalDividerCells s +
      (BinaryRationalArithmeticDivider.transitionTrace s).length := by
  have hg := rationalDivider_step_cells s
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticDivider.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinaryRationalArithmeticDivider.step] | omega)

theorem rationalDivider_cells_cost (n : ℕ) (s : BinaryRationalArithmeticDivider.State) :
    rationalDividerCells (BinaryRationalArithmeticDivider.advance n s) ≤
      rationalDividerCells s + BinaryRationalArithmeticDivider.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticDivider.advance, BinaryRationalArithmeticDivider.bitSteps]
  | succ n ih =>
    have hi := ih (BinaryRationalArithmeticDivider.step s)
    have hs := rationalDivider_step_cells_cost s
    simp only [BinaryRationalArithmeticDivider.advance, BinaryRationalArithmeticDivider.bitSteps]
    omega

def rationalDividerScratch (s : BinaryRationalArithmeticDivider.State) : Fin 68 → List Bool :=
  if s.phase = .zeroHalt then
    ![s.core.num.mul.factor,
      s.core.num.mul.shifted,
      s.core.num.mul.temp,
      s.core.num.mul.acc,
      s.core.num.mul.adder.left,
      s.core.num.mul.adder.right,
      s.core.num.mul.adder.work,
      s.core.num.mul.adder.out,
      s.core.num.norm.source,
      s.core.num.norm.work,
      s.core.num.norm.out,
      s.core.num.temp,
      s.core.den.mul.factor,
      s.core.den.mul.temp,
      s.core.den.mul.acc,
      s.core.den.mul.adder.left,
      s.core.den.mul.adder.right,
      s.core.den.mul.adder.work,
      s.core.den.mul.adder.out,
      s.core.den.norm.source,
      s.core.den.norm.work,
      s.core.den.norm.out,
      s.core.den.temp,
      s.core.norm.gcd.div.source,
      s.core.norm.gcd.div.bits,
      s.core.norm.gcd.div.divisor,
      s.core.norm.gcd.div.temp,
      s.core.norm.gcd.div.sub.left,
      s.core.norm.gcd.div.sub.right,
      s.core.norm.gcd.div.sub.work,
      s.core.norm.gcd.div.sub.out,
      s.core.norm.gcd.div.quot.source,
      s.core.norm.gcd.div.quot.work,
      s.core.norm.gcd.div.quot.out,
      s.core.norm.gcd.div.rem.source,
      s.core.norm.gcd.div.rem.work,
      s.core.norm.gcd.div.rem.out,
      s.core.norm.gcd.temp,
      s.core.norm.num.source,
      s.core.norm.num.bits,
      s.core.norm.num.divisor,
      s.core.norm.num.temp,
      s.core.norm.num.sub.left,
      s.core.norm.num.sub.right,
      s.core.norm.num.sub.work,
      s.core.norm.num.sub.out,
      s.core.norm.num.quot.source,
      s.core.norm.num.quot.work,
      s.core.norm.num.quot.out,
      s.core.norm.num.rem.source,
      s.core.norm.num.rem.work,
      s.core.norm.num.rem.out,
      s.core.norm.den.source,
      s.core.norm.den.bits,
      s.core.norm.den.divisor,
      s.core.norm.den.temp,
      s.core.norm.den.sub.left,
      s.core.norm.den.sub.right,
      s.core.norm.den.sub.work,
      s.core.norm.den.sub.out,
      s.core.norm.den.quot.source,
      s.core.norm.den.quot.work,
      s.core.norm.den.quot.out,
      s.core.norm.den.rem.source,
      s.core.norm.den.rem.work,
      s.core.norm.den.rem.out,
      s.core.norm.temp,
      s.core.temp]
  else
    ![s.core.num.mul.factor,
      s.core.num.mul.shifted,
      s.core.num.mul.temp,
      s.core.num.mul.acc,
      s.core.num.mul.adder.left,
      s.core.num.mul.adder.right,
      s.core.num.mul.adder.work,
      s.core.num.mul.adder.out,
      s.core.num.norm.source,
      s.core.num.norm.work,
      s.core.num.norm.out,
      s.core.num.temp,
      s.core.den.mul.factor,
      s.core.den.mul.shifted,
      s.core.den.mul.temp,
      s.core.den.mul.acc,
      s.core.den.mul.adder.left,
      s.core.den.mul.adder.right,
      s.core.den.mul.adder.work,
      s.core.den.mul.adder.out,
      s.core.den.norm.source,
      s.core.den.norm.work,
      s.core.den.norm.out,
      s.core.den.temp,
      s.core.norm.gcd.div.source,
      s.core.norm.gcd.div.bits,
      s.core.norm.gcd.div.divisor,
      s.core.norm.gcd.div.temp,
      s.core.norm.gcd.div.sub.left,
      s.core.norm.gcd.div.sub.right,
      s.core.norm.gcd.div.sub.work,
      s.core.norm.gcd.div.sub.out,
      s.core.norm.gcd.div.quot.source,
      s.core.norm.gcd.div.quot.work,
      s.core.norm.gcd.div.quot.out,
      s.core.norm.gcd.div.rem.source,
      s.core.norm.gcd.div.rem.work,
      s.core.norm.gcd.div.rem.out,
      s.core.norm.gcd.temp,
      s.core.norm.num.source,
      s.core.norm.num.bits,
      s.core.norm.num.divisor,
      s.core.norm.num.temp,
      s.core.norm.num.sub.left,
      s.core.norm.num.sub.right,
      s.core.norm.num.sub.work,
      s.core.norm.num.sub.out,
      s.core.norm.num.quot.source,
      s.core.norm.num.quot.work,
      s.core.norm.num.rem.source,
      s.core.norm.num.rem.work,
      s.core.norm.num.rem.out,
      s.core.norm.den.source,
      s.core.norm.den.bits,
      s.core.norm.den.divisor,
      s.core.norm.den.temp,
      s.core.norm.den.sub.left,
      s.core.norm.den.sub.right,
      s.core.norm.den.sub.work,
      s.core.norm.den.sub.out,
      s.core.norm.den.quot.source,
      s.core.norm.den.quot.work,
      s.core.norm.den.rem.source,
      s.core.norm.den.rem.work,
      s.core.norm.den.rem.out,
      s.core.norm.temp,
      s.core.temp,
      s.zeroDen]

theorem rationalDividerScratch_cells (s : BinaryRationalArithmeticDivider.State) :
    (∑ i, (rationalDividerScratch s i).length) +
      (BinaryRationalArithmeticDivider.output s).numerator.magnitude.length +
      (BinaryRationalArithmeticDivider.output s).denominator.length = rationalDividerCells s := by
  by_cases hp : s.phase = .zeroHalt
  all_goals
    simp [rationalDividerScratch, hp, Fin.sum_univ_succ, BinaryRationalArithmeticDivider.output,
      BinaryRationalArithmeticMultiplier.output, rationalDividerCells, rationalMultiplierCells, signedMultiplierCells,
      multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells]
    omega

theorem rationalDivider_cleanup (s : BinaryRationalArithmeticDivider.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalDividerScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalDividerScratch s)) ≤
        3 * (68 + rationalDividerCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalDividerScratch s)
  dsimp only at h
  refine ⟨68 + ∑ i, (rationalDividerScratch s i).length, h.2.1, ?_⟩
  have hc := rationalDividerScratch_cells s
  omega

theorem rationalDivider_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticDivider.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalDividerScratch (BinaryRationalArithmeticDivider.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalDividerScratch (BinaryRationalArithmeticDivider.advance n s))) ≤
        3 * (68 + rationalDividerCells s + BinaryRationalArithmeticDivider.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := rationalDivider_cleanup (BinaryRationalArithmeticDivider.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalDivider_cells_cost n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
