import IdentityTesting.FiniteAllocationUpperGeometry

/-! Rounding control derived from a feasible allocation at the original root.
The deliberately loose bound T >= 1/2 is sufficient for all upper sample counts. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting

theorem allocationCoordinate_reference_lower {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    1 - T ^ 2 * a ≤ allocationCoordinate T a a := by
  have hx := allocationCoordinate_range hT ha ha.le
  have hp := (unit_interval_powers hx.1 hx.2.le).2.2
  rw [allocationCoordinate_fourth hT ha ha.le] at hp
  have hden : 0 < a + T ^ 2 * a ^ 2 := by positivity
  apply le_trans _ hp
  apply (le_div_iff₀ hden).2
  have hnonneg : 0 ≤ T ^ 4 * a ^ 3 := by positivity
  nlinarith only [hnonneg]

theorem original_root_residual_bound {k : ℕ} (q : Probability (Fin k))
    (hq : ∀ i, 0 < q.mass i) {ε h : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hmax : ∀ i, q.mass i ≤ h) :
    1 - ε ≤ allocationRoot (extendFiniteLaw q) ε ^ 2 * h := by
  obtain ⟨hT, u, hu, hu1, hvalue, hmaximal⟩ :=
    exists_finite_allocation_optimizer_at_root q hq he0 he1
  have hfeasible := hmaximal q.mass q.nonneg q.total.le
  have hlower : 1 - allocationRoot (extendFiniteLaw q) ε ^ 2 * h ≤
      allocationObjective (allocationRoot (extendFiniteLaw q) ε) q.mass q.mass := by
    have hs : (∑ i, q.mass i * (1 - allocationRoot (extendFiniteLaw q) ε ^ 2 * h)) ≤
        ∑ i, q.mass i * allocationCoordinate (allocationRoot (extendFiniteLaw q) ε)
          (q.mass i) (q.mass i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (q.nonneg i)
      have hp := allocationCoordinate_reference_lower hT (hq i)
      have hm := mul_le_mul_of_nonneg_left (hmax i) (sq_nonneg (allocationRoot (extendFiniteLaw q) ε))
      linarith
    rw [← Finset.sum_mul, q.total, one_mul] at hs
    exact hs
  rw [hvalue] at hfeasible
  linarith

theorem original_root_ge_half {k : ℕ} (q : Probability (Fin k))
    (hq : ∀ i, 0 < q.mass i) {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    (1 : ℝ) / 2 ≤ allocationRoot (extendFiniteLaw q) ε := by
  have hmax : ∀ i, q.mass i ≤ largestMass (extendFiniteLaw q) := by
    intro i
    have h := largestIndex_spec (extendFiniteLaw q) i.val
    rw [← largestMass_eq_selected] at h
    simpa using h
  have h := original_root_residual_bound q hq he0 he1 hmax
  have hh := largestMass_pos (extendFiniteLaw q)
  have hT := (allocationRoot_spec (extendFiniteLaw q) he0 he1).1
  have hs : (1 : ℝ) / 2 ≤ allocationRoot (extendFiniteLaw q) ε ^ 2 := by
    have hp : ((1 : ℝ) / 2) * largestMass (extendFiniteLaw q) ≤
        allocationRoot (extendFiniteLaw q) ε ^ 2 * largestMass (extendFiniteLaw q) := by
      linarith
    exact (mul_le_mul_iff_left₀ hh).mp hp
  nlinarith

theorem ceil_scale_le {T K : ℝ} (hT : (1 : ℝ) / 2 ≤ T) (hK : 0 ≤ K) :
    (⌈K * T⌉₊ : ℝ) ≤ (K + 2) * T := by
  have hT0 : 0 ≤ T := by linarith
  have hc := Nat.ceil_lt_add_one (mul_nonneg hK hT0)
  nlinarith

end IdentityTesting.FiniteAllocationUpper
