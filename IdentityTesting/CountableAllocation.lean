import IdentityTesting.Target

/-! Bounds on the actual countable allocation supremum.  This module does not
assert that the supremum is attained or establish the root correspondence. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocation_term_bounds {a t u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    0 ≤ a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ∧
      a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤ a := by
  have hc : 0 ≤ t ^ 2 * a ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hr0 : 0 ≤ u / (u + t ^ 2 * a ^ 2) := div_nonneg hu (add_nonneg hu hc)
  have hr1 : u / (u + t ^ 2 * a ^ 2) ≤ 1 :=
    div_le_one_of_le₀ (le_add_of_nonneg_right hc) (add_nonneg hu hc)
  constructor
  · exact mul_nonneg ha (Real.rpow_nonneg hr0 _)
  · exact mul_le_of_le_one_right ha (Real.rpow_le_one hr0 hr1 (by norm_num))

theorem countableAllocationObjective_summable {a u : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hu : ∀ i, 0 ≤ u i) :
    Summable (fun i => a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) :=
  Summable.of_nonneg_of_le (fun i => (allocation_term_bounds (ha i) (hu i)).1)
    (fun i => (allocation_term_bounds (ha i) (hu i)).2) hasum

theorem countableAllocationObjective_bounds {a u : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hu : ∀ i, 0 ≤ u i) :
    0 ≤ countableAllocationObjective a t u ∧
      countableAllocationObjective a t u ≤ ∑' i, a i := by
  constructor
  · exact tsum_nonneg (fun i => (allocation_term_bounds (ha i) (hu i)).1)
  · exact (countableAllocationObjective_summable t ha hasum hu).tsum_le_tsum
      (fun i => (allocation_term_bounds (ha i) (hu i)).2) hasum

theorem zero_allocation_feasible : AllocationFeasible (fun _ => 0) := by
  exact ⟨fun _ => le_rfl, summable_zero, by simp⟩

@[simp] theorem countableAllocationObjective_zero (a : ℕ → ℝ) (t : ℝ) :
    countableAllocationObjective a t (fun _ => 0) = 0 := by
  simp [countableAllocationObjective]

theorem allocation_values_nonempty (a : ℕ → ℝ) (t : ℝ) :
    {v : ℝ | ∃ u, AllocationFeasible u ∧ v = countableAllocationObjective a t u}.Nonempty := by
  exact ⟨0, fun _ => 0, zero_allocation_feasible, (countableAllocationObjective_zero a t).symm⟩

theorem allocation_values_bddAbove {a : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    BddAbove {v : ℝ | ∃ u, AllocationFeasible u ∧ v = countableAllocationObjective a t u} := by
  refine ⟨∑' i, a i, ?_⟩
  rintro v ⟨u, hu, rfl⟩
  exact (countableAllocationObjective_bounds t ha hasum hu.1).2

theorem allocationD_bounds {a : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    0 ≤ allocationD a t ∧ allocationD a t ≤ ∑' i, a i := by
  constructor
  · exact le_csSup (allocation_values_bddAbove t ha hasum)
      ⟨fun _ => 0, zero_allocation_feasible, (countableAllocationObjective_zero a t).symm⟩
  · apply csSup_le (allocation_values_nonempty a t)
    rintro v ⟨u, hu, rfl⟩
    exact (countableAllocationObjective_bounds t ha hasum hu.1).2

theorem countableAllocationObjective_le_allocationD {a u : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hu : AllocationFeasible u) :
    countableAllocationObjective a t u ≤ allocationD a t :=
  le_csSup (allocation_values_bddAbove t ha hasum) ⟨u, hu, rfl⟩

theorem single_allocation_feasible (j : ℕ) :
    AllocationFeasible (fun i => if i = j then 1 else 0) := by
  refine ⟨fun i => ?_, (hasSum_ite_eq j (1 : ℝ)).summable, ?_⟩
  · by_cases h : i = j <;> simp [h]
  · exact le_of_eq (hasSum_ite_eq j (1 : ℝ)).tsum_eq

theorem allocationD_pos {a : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (hpos : ∃ j, 0 < a j) :
    0 < allocationD a t := by
  obtain ⟨j, hj⟩ := hpos
  let u : ℕ → ℝ := fun i => if i = j then 1 else 0
  have hu : AllocationFeasible u := single_allocation_feasible j
  have hterm : 0 < a j * (u j / (u j + t ^ 2 * a j ^ 2)) ^ (1 / 4 : ℝ) := by
    simp only [u, if_pos rfl]
    apply mul_pos hj
    apply Real.rpow_pos_of_pos
    exact div_pos zero_lt_one (by positivity)
  have hle := (countableAllocationObjective_summable t ha hasum hu.1).le_tsum j
    (fun i _ => (allocation_term_bounds (ha i) (hu.1 i)).1)
  exact hterm.trans_le (hle.trans (countableAllocationObjective_le_allocationD t ha hasum hu))

theorem allocation_term_antitone {a u t r : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (ht : 0 ≤ t) (htr : t ≤ r) :
    a * (u / (u + r ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤
      a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
  by_cases hz : u = 0
  · simp [hz]
  · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hsq : t ^ 2 ≤ r ^ 2 := by nlinarith
    have hden : u + t ^ 2 * a ^ 2 ≤ u + r ^ 2 * a ^ 2 :=
      add_le_add_left (mul_le_mul_of_nonneg_right hsq (sq_nonneg a)) u
    apply mul_le_mul_of_nonneg_left _ ha
    apply Real.rpow_le_rpow (div_nonneg hu (by positivity)) _ (by norm_num)
    exact div_le_div_of_nonneg_left hu (by positivity) hden

theorem allocationD_antitone {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) {t r : ℝ}
    (ht : 0 ≤ t) (htr : t ≤ r) : allocationD a r ≤ allocationD a t := by
  apply csSup_le (allocation_values_nonempty a r)
  rintro v ⟨u, hu, rfl⟩
  apply le_trans _ (countableAllocationObjective_le_allocationD t ha hasum hu)
  exact (countableAllocationObjective_summable r ha hasum hu.1).tsum_le_tsum
    (fun i => allocation_term_antitone (ha i) (hu.1 i) ht htr)
    (countableAllocationObjective_summable t ha hasum hu.1)

end IdentityTesting
