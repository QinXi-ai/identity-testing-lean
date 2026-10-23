import IdentityTesting.BinaryWorkspaceCost
import IdentityTesting.BinaryRationalArithmeticAdder

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

def rationalAdderCells (s : BinaryRationalArithmeticAdder.State) : ℕ :=
  rationalMultiplierCells s.base + signedMultiplierCells s.right + signedAdderCells s.adder + s.temp.length

set_option maxHeartbeats 1200000 in
theorem rationalAdder_step_cells (s : BinaryRationalArithmeticAdder.State) :
    rationalAdderCells (BinaryRationalArithmeticAdder.step s) ≤ rationalAdderCells s + 1 := by
  have hb := rationalMultiplier_step_cells s.base
  have hn := signedMultiplier_step_cells s.base.num
  have hd := signedMultiplier_step_cells s.base.den
  have hr := signedMultiplier_step_cells s.right
  have ha := signedAdder_step_cells s.adder
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticAdder.step, hp]
  all_goals (repeat' first | split | simp_all [rationalAdderCells, rationalMultiplierCells, signedMultiplierCells,
    multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells,
    signedAdderCells, signedComparisonCells] | omega)

theorem rationalAdder_step_cells_cost (s : BinaryRationalArithmeticAdder.State) :
    rationalAdderCells (BinaryRationalArithmeticAdder.step s) ≤ rationalAdderCells s +
      (BinaryRationalArithmeticAdder.transitionTrace s).length := by
  have hg := rationalAdder_step_cells s
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticAdder.transitionTrace, hp]
  all_goals (repeat' first | split | simp_all [BinaryRationalArithmeticAdder.step] | omega)

theorem rationalAdder_cells_cost (n : ℕ) (s : BinaryRationalArithmeticAdder.State) :
    rationalAdderCells (BinaryRationalArithmeticAdder.advance n s) ≤
      rationalAdderCells s + BinaryRationalArithmeticAdder.bitSteps n s := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticAdder.advance, BinaryRationalArithmeticAdder.bitSteps]
  | succ n ih =>
    have hi := ih (BinaryRationalArithmeticAdder.step s)
    have hs := rationalAdder_step_cells_cost s
    simp only [BinaryRationalArithmeticAdder.advance, BinaryRationalArithmeticAdder.bitSteps]
    omega

def rationalAdderScratch (s : BinaryRationalArithmeticAdder.State) : Fin 92 → List Bool :=
  ![s.base.num.mul.factor,
    s.base.num.mul.shifted,
    s.base.num.mul.temp,
    s.base.num.mul.acc,
    s.base.num.mul.adder.left,
    s.base.num.mul.adder.right,
    s.base.num.mul.adder.work,
    s.base.num.mul.adder.out,
    s.base.num.norm.source,
    s.base.num.norm.work,
    s.base.num.norm.out,
    s.base.num.temp,
    s.base.den.mul.factor,
    s.base.den.mul.shifted,
    s.base.den.mul.temp,
    s.base.den.mul.acc,
    s.base.den.mul.adder.left,
    s.base.den.mul.adder.right,
    s.base.den.mul.adder.work,
    s.base.den.mul.adder.out,
    s.base.den.norm.source,
    s.base.den.norm.work,
    s.base.den.norm.out,
    s.base.den.temp,
    s.base.norm.gcd.div.source,
    s.base.norm.gcd.div.bits,
    s.base.norm.gcd.div.divisor,
    s.base.norm.gcd.div.temp,
    s.base.norm.gcd.div.sub.left,
    s.base.norm.gcd.div.sub.right,
    s.base.norm.gcd.div.sub.work,
    s.base.norm.gcd.div.sub.out,
    s.base.norm.gcd.div.quot.source,
    s.base.norm.gcd.div.quot.work,
    s.base.norm.gcd.div.quot.out,
    s.base.norm.gcd.div.rem.source,
    s.base.norm.gcd.div.rem.work,
    s.base.norm.gcd.div.rem.out,
    s.base.norm.gcd.temp,
    s.base.norm.num.source,
    s.base.norm.num.bits,
    s.base.norm.num.divisor,
    s.base.norm.num.temp,
    s.base.norm.num.sub.left,
    s.base.norm.num.sub.right,
    s.base.norm.num.sub.work,
    s.base.norm.num.sub.out,
    s.base.norm.num.quot.source,
    s.base.norm.num.quot.work,
    s.base.norm.num.rem.source,
    s.base.norm.num.rem.work,
    s.base.norm.num.rem.out,
    s.base.norm.den.source,
    s.base.norm.den.bits,
    s.base.norm.den.divisor,
    s.base.norm.den.temp,
    s.base.norm.den.sub.left,
    s.base.norm.den.sub.right,
    s.base.norm.den.sub.work,
    s.base.norm.den.sub.out,
    s.base.norm.den.quot.source,
    s.base.norm.den.quot.work,
    s.base.norm.den.rem.source,
    s.base.norm.den.rem.work,
    s.base.norm.den.rem.out,
    s.base.norm.temp,
    s.base.temp,
    s.right.mul.factor,
    s.right.mul.shifted,
    s.right.mul.temp,
    s.right.mul.acc,
    s.right.mul.adder.left,
    s.right.mul.adder.right,
    s.right.mul.adder.work,
    s.right.mul.adder.out,
    s.right.norm.source,
    s.right.norm.work,
    s.right.norm.out,
    s.right.temp,
    s.adder.left,
    s.adder.right,
    s.adder.temp,
    s.adder.compare.left,
    s.adder.compare.right,
    s.adder.arith.left,
    s.adder.arith.right,
    s.adder.arith.work,
    s.adder.arith.out,
    s.adder.norm.source,
    s.adder.norm.work,
    s.adder.norm.out,
    s.temp]

theorem rationalAdderScratch_cells (s : BinaryRationalArithmeticAdder.State) :
    (∑ i, (rationalAdderScratch s i).length) + s.base.norm.num.quot.out.length + s.base.norm.den.quot.out.length =
      rationalAdderCells s := by
  simp [rationalAdderScratch, Fin.sum_univ_succ, rationalAdderCells, rationalMultiplierCells, signedMultiplierCells,
    multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells,
    signedAdderCells, signedComparisonCells]
  omega

theorem rationalAdder_cleanup (s : BinaryRationalArithmeticAdder.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalAdderScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalAdderScratch s)) ≤
        3 * (92 + rationalAdderCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalAdderScratch s)
  dsimp only at h
  refine ⟨92 + ∑ i, (rationalAdderScratch s i).length, h.2.1, ?_⟩
  have hc := rationalAdderScratch_cells s
  omega

theorem rationalAdder_cleanup_cost (n : ℕ) (s : BinaryRationalArithmeticAdder.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalAdderScratch (BinaryRationalArithmeticAdder.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalAdderScratch (BinaryRationalArithmeticAdder.advance n s))) ≤
        3 * (92 + rationalAdderCells s + BinaryRationalArithmeticAdder.bitSteps n s) := by
  obtain ⟨fuel, hc, hb⟩ := rationalAdder_cleanup (BinaryRationalArithmeticAdder.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalAdder_cells_cost n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
