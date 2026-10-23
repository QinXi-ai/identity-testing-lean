import IdentityTesting.BinaryWorkspaceNormalizationAdapter
import IdentityTesting.BinaryRationalArithmeticMultiplier

namespace IdentityTesting.BinaryWorkspaceAdapters
open BinaryWorkspaceGrowth
open scoped BigOperators

def rationalMultiplierCells (s : BinaryRationalArithmeticMultiplier.State) : ℕ :=
  signedMultiplierCells s.num + signedMultiplierCells s.den + rationalNormalizationCells s.norm + s.temp.length

theorem rationalMultiplier_step_cells (s : BinaryRationalArithmeticMultiplier.State) :
    rationalMultiplierCells (BinaryRationalArithmeticMultiplier.step s) ≤ rationalMultiplierCells s + 1 := by
  have hn := signedMultiplier_step_cells s.num
  have hd := signedMultiplier_step_cells s.den
  have hr := rationalNormalization_step_cells s.norm
  cases hp : s.phase <;> simp only [BinaryRationalArithmeticMultiplier.step, hp]
  all_goals (repeat' first | split | simp_all [rationalMultiplierCells, signedMultiplierCells,
    multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells] | omega)

theorem rationalMultiplier_advance_cells (n : ℕ) (s : BinaryRationalArithmeticMultiplier.State) :
    rationalMultiplierCells (BinaryRationalArithmeticMultiplier.advance n s) ≤ rationalMultiplierCells s + n := by
  induction n generalizing s with
  | zero => simp [BinaryRationalArithmeticMultiplier.advance]
  | succ n ih =>
    have hi := ih (BinaryRationalArithmeticMultiplier.step s)
    have hs := rationalMultiplier_step_cells s
    simp only [BinaryRationalArithmeticMultiplier.advance]
    omega

/-- The same physical scratch stacks; the two output stacks are untouched. -/
def rationalMultiplierScratch (s : BinaryRationalArithmeticMultiplier.State) : Fin 67 → List Bool :=
  ![s.num.mul.factor,
    s.num.mul.shifted,
    s.num.mul.temp,
    s.num.mul.acc,
    s.num.mul.adder.left,
    s.num.mul.adder.right,
    s.num.mul.adder.work,
    s.num.mul.adder.out,
    s.num.norm.source,
    s.num.norm.work,
    s.num.norm.out,
    s.num.temp,
    s.den.mul.factor,
    s.den.mul.shifted,
    s.den.mul.temp,
    s.den.mul.acc,
    s.den.mul.adder.left,
    s.den.mul.adder.right,
    s.den.mul.adder.work,
    s.den.mul.adder.out,
    s.den.norm.source,
    s.den.norm.work,
    s.den.norm.out,
    s.den.temp,
    s.norm.gcd.div.source,
    s.norm.gcd.div.bits,
    s.norm.gcd.div.divisor,
    s.norm.gcd.div.temp,
    s.norm.gcd.div.sub.left,
    s.norm.gcd.div.sub.right,
    s.norm.gcd.div.sub.work,
    s.norm.gcd.div.sub.out,
    s.norm.gcd.div.quot.source,
    s.norm.gcd.div.quot.work,
    s.norm.gcd.div.quot.out,
    s.norm.gcd.div.rem.source,
    s.norm.gcd.div.rem.work,
    s.norm.gcd.div.rem.out,
    s.norm.gcd.temp,
    s.norm.num.source,
    s.norm.num.bits,
    s.norm.num.divisor,
    s.norm.num.temp,
    s.norm.num.sub.left,
    s.norm.num.sub.right,
    s.norm.num.sub.work,
    s.norm.num.sub.out,
    s.norm.num.quot.source,
    s.norm.num.quot.work,
    s.norm.num.rem.source,
    s.norm.num.rem.work,
    s.norm.num.rem.out,
    s.norm.den.source,
    s.norm.den.bits,
    s.norm.den.divisor,
    s.norm.den.temp,
    s.norm.den.sub.left,
    s.norm.den.sub.right,
    s.norm.den.sub.work,
    s.norm.den.sub.out,
    s.norm.den.quot.source,
    s.norm.den.quot.work,
    s.norm.den.rem.source,
    s.norm.den.rem.work,
    s.norm.den.rem.out,
    s.norm.temp,
    s.temp]

theorem rationalMultiplierScratch_cells (s : BinaryRationalArithmeticMultiplier.State) :
    (∑ i, (rationalMultiplierScratch s i).length) + s.norm.num.quot.out.length + s.norm.den.quot.out.length =
      rationalMultiplierCells s := by
  simp [rationalMultiplierScratch, Fin.sum_univ_succ, rationalMultiplierCells, signedMultiplierCells,
    multiplierCells, normalizerCells, rationalNormalizationCells, gcdCells, divisionCells, adderCells]
  omega

theorem rationalMultiplier_cleanup (s : BinaryRationalArithmeticMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch s))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch s)) ≤
        3 * (67 + rationalMultiplierCells s) := by
  have h := BinaryWorkspaceCleanup.workspace_cleanup (rationalMultiplierScratch s)
  dsimp only at h
  refine ⟨67 + ∑ i, (rationalMultiplierScratch s i).length, h.2.1, ?_⟩
  have hc := rationalMultiplierScratch_cells s
  omega

theorem rationalMultiplier_cleanup_after (n : ℕ) (s : BinaryRationalArithmeticMultiplier.State) :
    ∃ fuel, (∀ i, (BinaryWorkspaceCleanup.advance fuel
      (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch (BinaryRationalArithmeticMultiplier.advance n s)))).tapes i = []) ∧
      BinaryWorkspaceCleanup.bitSteps fuel
        (BinaryWorkspaceCleanup.initial (rationalMultiplierScratch (BinaryRationalArithmeticMultiplier.advance n s))) ≤
        3 * (67 + rationalMultiplierCells s + n) := by
  obtain ⟨fuel, hc, hb⟩ := rationalMultiplier_cleanup (BinaryRationalArithmeticMultiplier.advance n s)
  refine ⟨fuel, hc, ?_⟩
  have hg := rationalMultiplier_advance_cells n s
  omega

end IdentityTesting.BinaryWorkspaceAdapters
