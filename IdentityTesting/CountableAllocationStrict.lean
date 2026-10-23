import IdentityTesting.CountableAllocationExistence

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocation_term_strict_antitone {a u t r : ℝ}
    (ha : 0 < a) (hu : 0 < u) (ht : 0 ≤ t) (htr : t < r) :
    a * (u / (u + r ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) <
      a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
  have hsq : t ^ 2 < r ^ 2 := by nlinarith
  have hden : u + t ^ 2 * a ^ 2 < u + r ^ 2 * a ^ 2 :=
    add_lt_add_left (mul_lt_mul_of_pos_right hsq (sq_pos_of_pos ha)) u
  apply mul_lt_mul_of_pos_left _ ha
  apply Real.rpow_lt_rpow (div_nonneg hu.le (by positivity)) _ (by norm_num)
  exact div_lt_div_of_pos_left hu (by positivity) hden

/-- Strict decrease is proved at the actual maximizer for the larger parameter,
not inferred from pointwise strict inequalities under an unattained supremum. -/
theorem allocationD_strict_antitone {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hpos : ∃ i, 0 < a i)
    {t r : ℝ} (ht : 0 < t) (htr : t < r) : allocationD a r < allocationD a t := by
  obtain ⟨u, hu, hvalue⟩ := allocationD_attained ha hasum (ht.trans htr)
  have hobj : 0 < countableAllocationObjective a r u := by
    rw [hvalue]
    exact allocationD_pos r ha hasum hpos
  have hex : ∃ j, 0 < a j * (u j / (u j + r ^ 2 * a j ^ 2)) ^ (1 / 4 : ℝ) := by
    by_contra h
    have hz : (fun j => a j * (u j / (u j + r ^ 2 * a j ^ 2)) ^ (1 / 4 : ℝ)) =
        fun _ => 0 := by
      funext j
      exact le_antisymm (le_of_not_gt (fun hj => h ⟨j, hj⟩))
        (allocation_term_bounds (ha j) (hu.1 j)).1
    unfold countableAllocationObjective at hobj
    rw [hz] at hobj
    simpa using hobj
  obtain ⟨j, hj⟩ := hex
  have haj : 0 < a j := by
    by_contra h
    have hz : a j = 0 := le_antisymm (le_of_not_gt h) (ha j)
    simp [hz] at hj
  have huj : 0 < u j := by
    by_contra h
    have hz : u j = 0 := le_antisymm (le_of_not_gt h) (hu.1 j)
    simp [hz] at hj
  have hstrict : countableAllocationObjective a r u < countableAllocationObjective a t u := by
    exact Summable.tsum_lt_tsum
      (fun i => allocation_term_antitone (ha i) (hu.1 i) ht.le htr.le)
      (allocation_term_strict_antitone haj huj ht.le htr)
      (countableAllocationObjective_summable r ha hasum hu.1)
      (countableAllocationObjective_summable t ha hasum hu.1)
  rw [hvalue] at hstrict
  exact hstrict.trans_le (countableAllocationObjective_le_allocationD t ha hasum hu)

theorem allocationD_strictAntiOn {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hpos : ∃ i, 0 < a i) :
    StrictAntiOn (allocationD a) (Set.Ioi 0) := by
  intro t ht r hr htr
  exact allocationD_strict_antitone ha hasum hpos ht htr

end IdentityTesting
