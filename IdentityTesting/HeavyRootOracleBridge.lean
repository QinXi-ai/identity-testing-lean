import IdentityTesting.HeavyRootOracleGeometry
import IdentityTesting.HeavyFiniteBridge

open scoped BigOperators
namespace IdentityTesting.RationalComputation
open FiniteTesting HeavySignedFamily
noncomputable section

theorem finiteHeavyRoot_eq_original_heavyRoot {k : ℕ}
    (p : Probability (Fin (k + 2))) (hp : ∀ i, 0 < p.mass i)
    (hR : tailTotal p ≤ (1 : ℝ) / 4) {e : ℝ} (he : 0 < e) :
    finiteHeavyRoot (fun i : Fin (k + 1) => p.mass i.succ) e =
      heavyRoot (extendFiniteLaw p) e := by
  let a : Fin (k + 1) → ℝ := fun i => p.mass i.succ
  have ha : ∀ i, 0 < a i := fun i => hp i.succ
  have hr : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have htotal := reference_head_tail p
  have hRform : 1 - p.mass 0 = ∑ i, a i := by
    change 1 - p.mass 0 = tailTotal p
    linarith only [htotal]
  have hlarge : largestMass (extendFiniteLaw p) < 1 := by
    rw [largestMass_extendFiniteLaw_heavy p hR]
    linarith only [hRform, hr]
  have hroot := heavyRoot_spec (extendFiniteLaw p) hlarge he
  let T := heavyRoot (extendFiniteLaw p) e
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer hroot.1 ha
  have hvTail := allocationD_extendFiniteTailVector_eq_optimizer hroot.1 ha
    ⟨fun i => (hu0 i).le, hu1.le⟩ hmax
  have hv := allocationD_extendFiniteVector_eq_optimizer hroot.1 ha
    ⟨fun i => (hu0 i).le, hu1.le⟩ hmax
  have heq := heavyRoot_equation (extendFiniteLaw p) hlarge he
  rw [tailMasses_extendFiniteLaw_heavy p hR, largestMass_extendFiniteLaw_heavy p hR,
    hRform] at heq
  have hf : finiteHeavyFunction a T = e := by
    dsimp only [finiteHeavyFunction, T]
    rw [hv]
    rw [hvTail] at heq
    exact heq
  exact positive_sublevel_sInf_eq (finiteHeavyFunction_strictAnti a (fun i => (ha i).le) hr)
    hroot.1 hf

end
end IdentityTesting.RationalComputation
