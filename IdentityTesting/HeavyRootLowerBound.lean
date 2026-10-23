import IdentityTesting.HeavyFiniteBridge
import IdentityTesting.HeavyAllocationLowerBound

/-! # Interior heavy lower bound at the original countable heavy root -/

noncomputable section
namespace IdentityTesting

open FiniteTesting HeavySignedFamily HeavyLowerGeometry

theorem no_identityTest_of_finite_heavyRoot {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε0 : 0 < ε) (hεR : ε ≤ tailTotal q)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * heavyRoot (extendFiniteLaw q) ε) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  obtain ⟨hT, x, hx, hradius, hbudget⟩ := exists_finite_heavy_coordinates_at_root q hq hR0 hR hε0
  exact no_identityTest_of_heavy_allocation_coordinates q x (heavyRoot (extendFiniteLaw q) ε) ε
    hT hq (fun i => ⟨(hx i).1.le, (hx i).2⟩) hR0 hR hbudget hradius hεR n hn

end IdentityTesting
