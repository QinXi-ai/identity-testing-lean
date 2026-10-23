import IdentityTesting.HeavyFiniteBridge
import IdentityTesting.FiniteAllocationUpper

/-! KKT witnesses and count scale for the original finite heavy root, used by
the actual heavy-head upper tests. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting HeavySignedFamily

theorem exists_heavy_upper_coordinates_at_root {k : ℕ}
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε : 0 < ε) :
    0 < heavyRoot (extendFiniteLaw q) ε ∧
      ∃ (x : Fin k → ℝ) (β : ℝ), (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i.succ * x i) + Real.sqrt (tailTotal q / heavyRoot (extendFiniteLaw q) ε) = ε ∧
        0 < β ∧ (∀ i, q.mass i.succ * x i ^ 3 = β * (1 - x i ^ 4) ^ 2) ∧
        1 = heavyRoot (extendFiniteLaw q) ε ^ 2 * β *
          ∑ i, q.mass i.succ * x i * (1 - x i ^ 4) := by
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hn
    subst k
    simp only [tailTotal, Finset.univ_eq_empty, Finset.sum_empty] at hR0
    exact (lt_irrefl 0) hR0
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have htotal := reference_head_tail q
  have hlarge : largestMass (extendFiniteLaw q) < 1 := by
    rw [largestMass_extendFiniteLaw_heavy q hR]
    linarith
  have hroot := heavyRoot_spec (extendFiniteLaw q) hlarge hε
  let T := heavyRoot (extendFiniteLaw q) ε
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer hroot.1
    (fun i : Fin k => hq i.succ)
  obtain ⟨β, hβ, hkkt, hbudget⟩ := allocation_optimizer_kkt hroot.1
    (fun i : Fin k => hq i.succ) hu0 hu1 hmax
  have hvalue := allocationD_extendFiniteTailVector_eq_optimizer hroot.1
    (fun i : Fin k => hq i.succ) ⟨(fun i => (hu0 i).le), hu1.le⟩ hmax
  have hrootEq := heavyRoot_equation (extendFiniteLaw q) hlarge hε
  rw [tailMasses_extendFiniteLaw_heavy q hR, largestMass_extendFiniteLaw_heavy q hR, hvalue] at hrootEq
  have hRformula : 1 - q.mass 0 = tailTotal q := by linarith
  rw [hRformula] at hrootEq
  let x : Fin k → ℝ := fun i => allocationCoordinate T (q.mass i.succ) (u i)
  refine ⟨hroot.1, x, β, ?_, hrootEq, hβ, hkkt, hbudget⟩
  intro i
  exact ⟨allocationCoordinate_pos hroot.1 (hq i.succ) (hu0 i),
    (allocationCoordinate_range hroot.1 (hq i.succ) (hu0 i).le).2⟩

theorem heavy_count_scale {R T g : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 4)
    (hT : 0 < T) (hg : g = Real.sqrt (R / T)) (hgR : g ≤ R) :
    0 < g ∧ 4 ≤ T ∧ 1 ≤ T * g ∧ 1 / T ≤ g := by
  have hg0 : 0 < g := by rw [hg]; exact Real.sqrt_pos.mpr (div_pos hR hT)
  have hs : g ^ 2 = R / T := by rw [hg]; exact Real.sq_sqrt (div_nonneg hR.le hT.le)
  have hsq : T * g ^ 2 = R := by have h := (eq_div_iff (ne_of_gt hT)).mp hs; nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_left hgR hg0.le
  have hmg : T * g ^ 2 ≤ T * (g * R) := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hm hT.le
  have hTg : 1 ≤ T * g := by
    have hc : R * 1 ≤ R * (T * g) := by nlinarith only [hmg, hsq]
    exact (mul_le_mul_iff_right₀ hR).mp hc
  have hTR := mul_le_mul_of_nonneg_left hgR hT.le
  have hT4 : 4 ≤ T := by nlinarith [mul_le_mul_of_nonneg_left hR1 hT.le]
  refine ⟨hg0, hT4, hTg, ?_⟩
  apply (div_le_iff₀ hT).2
  nlinarith only [hTg]

end IdentityTesting.HeavyUpper
