import IdentityTesting.AllocationExistence

/-!
# Saturation of the allocation budget

The actual coordinate is strictly increasing in its nonnegative allocation.
Increasing one coordinate of a finite allocation therefore strictly improves
the positive weighted objective.  Every global maximizer on a nonempty finite
budget simplex must consequently spend the full budget.  The final existence
theorem obtains its maximizing witness from compactness, then proves saturation;
it does not take saturation or existence as an additional premise.
-/

namespace IdentityTesting

open scoped BigOperators

/-- The rational coordinate underlying the fourth root is strictly increasing
on nonnegative allocations when its offset is positive. -/
theorem allocation_ratio_lt {u v c : ℝ} (hc : 0 < c) (hu : 0 ≤ u) (huv : u < v) :
    u / (u + c) < v / (v + c) := by
  have hv : 0 ≤ v := le_trans hu (le_of_lt huv)
  have hdu : 0 < u + c := add_pos_of_nonneg_of_pos hu hc
  have hdv : 0 < v + c := add_pos_of_nonneg_of_pos hv hc
  apply (div_lt_div_iff₀ hdu hdv).2
  have hproduct : 0 < (v - u) * c := mul_pos (sub_pos.mpr huv) hc
  nlinarith only [hproduct]

/-- The concrete coordinate in the allocation objective strictly increases with
the original nonnegative allocation. -/
theorem allocationCoordinate_lt {t a u v : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) (huv : u < v) :
    allocationCoordinate t a u < allocationCoordinate t a v := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  have hratio := allocation_ratio_lt hc hu huv
  have hr0 := (allocation_ratio_range hc hu).1
  unfold allocationCoordinate
  exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg _)
    (Real.sqrt_lt_sqrt hr0 hratio)

theorem allocationCoordinate_strictMonoOn {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    StrictMonoOn (allocationCoordinate t a) (Set.Ici 0) := by
  intro u hu v hv huv
  exact allocationCoordinate_lt ht ha hu huv

/-- Updating one coordinate by an increment adds exactly that increment to the
finite total budget. -/
theorem allocation_sum_update_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (j : ι) (δ : ℝ) :
    (∑ i, Function.update u j (u j + δ) i) = (∑ i, u i) + δ := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j) u]
  ring

/-- A positive increment at any coordinate strictly improves the actual
positive weighted objective. -/
theorem allocationObjective_update_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu : ∀ i, 0 ≤ u i) (j : ι) {δ : ℝ} (hδ : 0 < δ) :
    allocationObjective t a u <
      allocationObjective t a (Function.update u j (u j + δ)) := by
  classical
  have hcoord : allocationCoordinate t (a j) (u j) <
      allocationCoordinate t (a j) (u j + δ) :=
    allocationCoordinate_lt ht (ha j) (hu j) (by linarith)
  have hweighted := mul_lt_mul_of_pos_left hcoord (ha j)
  unfold allocationObjective
  apply Finset.sum_lt_sum
  · intro i hi
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using le_of_lt hweighted
    · simp only [Function.update_of_ne hij, le_refl]
  · exact ⟨j, Finset.mem_univ j, by simpa only [Function.update_self] using hweighted⟩

/-- Every actual global maximizer on a nonempty finite allocation simplex has
saturated budget. -/
theorem allocation_maximizer_saturated {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    (∑ i, u i) = 1 := by
  classical
  by_contra hne
  have hsumlt : (∑ i, u i) < 1 := lt_of_le_of_ne hu1 hne
  let δ : ℝ := 1 - ∑ i, u i
  have hδ : 0 < δ := sub_pos.mpr hsumlt
  let j : ι := Classical.choice (inferInstance : Nonempty ι)
  let v : ι → ℝ := Function.update u j (u j + δ)
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [v, Function.update_self] using add_nonneg (hu0 j) (le_of_lt hδ)
    · simpa only [v, Function.update_of_ne hij] using hu0 i
  have hv1 : (∑ i, v i) ≤ 1 := by
    change (∑ i, Function.update u j (u j + δ) i) ≤ 1
    rw [allocation_sum_update_add]
    dsimp only [δ]
    linarith
  have hbetter : allocationObjective t a u < allocationObjective t a v :=
    allocationObjective_update_lt ht ha hu0 j hδ
  exact (not_lt_of_ge (hmax v hv0 hv1)) hbetter

/-- The same saturation result with the literal real-power objective from
`eq:main-D`, making the original caller interface explicit. -/
theorem manuscript_allocation_maximizer_saturated {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
        ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) :
    (∑ i, u i) = 1 := by
  apply allocation_maximizer_saturated ht ha hu0 hu1
  intro v hv0 hv1
  rw [allocationObjective_eq_rpow ht ha hv0, allocationObjective_eq_rpow ht ha hu0]
  exact hmax v hv0 hv1

/-- The original allocation problem has an actual optimizer with full budget;
both existence and saturation are proved from the positive masses and time. -/
theorem exists_saturated_allocation_maximizer {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) = 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        allocationObjective t a v ≤ allocationObjective t a u := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_allocation_maximizer ht ha
  exact ⟨u, hu0, allocation_maximizer_saturated ht ha hu0 hu1 hmax, hmax⟩

/-- Full-budget optimizer existence written with exactly the manuscript's
real-power objective. -/
theorem exists_manuscript_saturated_allocation_maximizer
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) = 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_manuscript_allocation_maximizer ht ha
  exact ⟨u, hu0, manuscript_allocation_maximizer_saturated ht ha hu0 hu1 hmax, hmax⟩

end IdentityTesting
