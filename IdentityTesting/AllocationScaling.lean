import IdentityTesting.CountableAllocation

/-! Exact mass scaling for the original countable allocation supremum.
The domain includes zero masses, zero scale, and arbitrary real time. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem countableAllocationObjective_mass_scale (a u : ℕ → ℝ) (c t : ℝ) :
    countableAllocationObjective (fun i => c * a i) t u =
      c * countableAllocationObjective a (c * t) u := by
  unfold countableAllocationObjective
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  have h : t ^ 2 * (c * a i) ^ 2 = (c * t) ^ 2 * a i ^ 2 := by ring
  rw [h]
  ring

/-- `count:scaling`, including the zero scale boundary. No probability
normalization, strict positivity of coordinates, or optimizer is assumed. -/
theorem allocationD_mass_scale {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hasum : Summable a) {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    allocationD (fun i => c * a i) t = c * allocationD a (c * t) := by
  have hca : ∀ i, 0 ≤ c * a i := fun i => mul_nonneg hc (ha i)
  have hcsum : Summable (fun i => c * a i) := hasum.mul_left c
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst c
    have hbound := allocationD_bounds t hca hcsum
    simpa using le_antisymm (by simpa using hbound.2) hbound.1
  · apply le_antisymm
    · apply csSup_le (allocation_values_nonempty _ _)
      rintro v ⟨u, hu, rfl⟩
      rw [countableAllocationObjective_mass_scale]
      exact mul_le_mul_of_nonneg_left
        (countableAllocationObjective_le_allocationD _ ha hasum hu) hc
    · rw [mul_comm c]
      apply (le_div_iff₀ hcpos).mp
      apply csSup_le (allocation_values_nonempty _ _)
      rintro v ⟨u, hu, rfl⟩
      apply (le_div_iff₀ hcpos).mpr
      rw [mul_comm, ← countableAllocationObjective_mass_scale]
      exact countableAllocationObjective_le_allocationD t hca hcsum hu

end IdentityTesting
