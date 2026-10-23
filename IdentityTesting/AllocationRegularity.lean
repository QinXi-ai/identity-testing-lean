import IdentityTesting.AllocationSaturation

/-!
# Interiority of actual finite allocation maximizers

The boundary improvement uses concrete feasible allocations.  Shrinking an old
allocation by a factor `k` in `[0,1]` preserves at least `k` times its objective.
At a zero coordinate the new fourth-root gain dominates the linear shrinkage
loss.  This rules out every zero coordinate of a genuine global optimizer.
-/

namespace IdentityTesting

open scoped BigOperators

/-- Shrinking an allocation by `k ∈ [0,1]` retains at least `k` times its
fourth-root coordinate. -/
theorem allocationCoordinate_scale_le {t a u k : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    k * allocationCoordinate t a u ≤ allocationCoordinate t a (k * u) := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  have hku : 0 ≤ k * u := mul_nonneg hk0 hu
  have hden : k * u + t ^ 2 * a ^ 2 ≤ u + t ^ 2 * a ^ 2 := by
    nlinarith only [mul_nonneg hu (sub_nonneg.mpr hk1)]
  have hratio : k * (u / (u + t ^ 2 * a ^ 2)) ≤
      k * u / (k * u + t ^ 2 * a ^ 2) := by
    calc
      k * (u / (u + t ^ 2 * a ^ 2)) = k * u / (u + t ^ 2 * a ^ 2) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left hku (add_pos_of_nonneg_of_pos hku hc) hden
  have hk4 : k ^ 4 ≤ k := pow_le_of_le_one hk0 hk1 (by norm_num)
  have hr0 := (allocation_ratio_range hc hu).1
  have hpow : (k * allocationCoordinate t a u) ^ 4 ≤
      (allocationCoordinate t a (k * u)) ^ 4 := by
    rw [mul_pow, allocationCoordinate_fourth ht ha hu,
      allocationCoordinate_fourth ht ha hku]
    exact (mul_le_mul_of_nonneg_right hk4 hr0).trans hratio
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (allocationCoordinate_range ht ha hku).1 hpow

theorem allocationObjective_nonneg {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu : ∀ i, 0 ≤ u i) : 0 ≤ allocationObjective t a u := by
  unfold allocationObjective
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (le_of_lt (ha i)) (allocationCoordinate_range ht (ha i) (hu i)).1

/-- The actual weighted objective obeys the same scaling lower bound. -/
theorem allocationObjective_scale_le {ι : Type*} [Fintype ι]
    {t k : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu : ∀ i, 0 ≤ u i) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    k * allocationObjective t a u ≤
      allocationObjective t a (fun i => k * u i) := by
  unfold allocationObjective
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_left
    (allocationCoordinate_scale_le ht (ha i) (hu i) hk0 hk1) (le_of_lt (ha i))
  nlinarith only [h]

/-- A sufficiently small new transformed coordinate yields more weighted gain
than the shrinkage loss it charges to the budget.  The witness is derived from
continuity of the explicit rational cost divided by the coordinate. -/
theorem exists_allocation_entry_gain {t a B : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧ 0 < allocationCost t a x ∧
      allocationCost t a x < 1 ∧ allocationCost t a x * B < a * x := by
  let g : ℝ → ℝ := fun x => t ^ 2 * a ^ 2 * x ^ 3 / (1 - x ^ 4)
  have hg : ContinuousAt g 0 := by
    apply ContinuousAt.div
    · exact continuousAt_const.mul (continuousAt_id.pow 3)
    · exact continuousAt_const.sub (continuousAt_id.pow 4)
    · norm_num
  let q : ℝ := min (a / (B + 1)) (1 / 2)
  have hq : 0 < q := lt_min (div_pos ha (by linarith)) (by norm_num)
  obtain ⟨ε, hε, hclose⟩ := Metric.continuousAt_iff.mp hg q hq
  let x : ℝ := min ε 1 / 2
  have hx0 : 0 < x := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hxmin : x < ε := by
    have h := min_le_left ε (1 : ℝ)
    dsimp only [x]
    linarith
  have hx1 : x < 1 := by
    have h := min_le_right ε (1 : ℝ)
    dsimp only [x]
    linarith
  have hdist : dist x 0 < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hx0] using hxmin
  have hgq : g x < q := by
    have h := hclose hdist
    have hgzero : g 0 = 0 := by simp [g]
    have habs : |g x| < q := by
      simpa only [Real.dist_eq, hgzero, sub_zero] using h
    exact (abs_lt.mp habs).2
  have hden : 0 < 1 - x ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  have hg0 : 0 ≤ g x := by
    dsimp only [g]
    positivity
  have hga : g x < a / (B + 1) := hgq.trans_le (min_le_left _ _)
  have hghalf : g x < 1 / 2 := hgq.trans_le (min_le_right _ _)
  have hgB : g x * B < a := by
    have h := (lt_div_iff₀ (by linarith : 0 < B + 1)).1 hga
    nlinarith only [h, hg0]
  have hcost : allocationCost t a x = x * g x := by
    unfold allocationCost
    dsimp only [g]
    ring
  have hcostpos : 0 < allocationCost t a x := by
    unfold allocationCost
    positivity
  have hcostlt : allocationCost t a x < 1 := by
    rw [hcost]
    have h := mul_pos hx0 (sub_pos.mpr hghalf)
    nlinarith only [h, hx1]
  have hgain : allocationCost t a x * B < a * x := by
    rw [hcost]
    have h := mul_pos hx0 (sub_pos.mpr hgB)
    nlinarith only [h]
  exact ⟨x, hx0, hx1, hcostpos, hcostlt, hgain⟩

@[simp]
theorem allocationCoordinate_zero (t a : ℝ) : allocationCoordinate t a 0 = 0 := by
  simp [allocationCoordinate]

/-- Updating a formerly zero coordinate adds exactly the new coordinate's
weighted objective contribution. -/
theorem allocationObjective_update_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℝ} {a u : ι → ℝ} {j : ι} (huj : u j = 0) (s : ℝ) :
    allocationObjective t a (Function.update u j s) =
      allocationObjective t a u + a j * allocationCoordinate t (a j) s := by
  have hfun : (fun i => a i * allocationCoordinate t (a i) (Function.update u j s i)) =
      Function.update (fun i => a i * allocationCoordinate t (a i) (u i)) j
        (a j * allocationCoordinate t (a j) (u j) + a j * allocationCoordinate t (a j) s) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self, huj, allocationCoordinate_zero, mul_zero, zero_add]
    · simp only [Function.update_of_ne hij]
  unfold allocationObjective
  rw [hfun, allocation_sum_update_add]

/-- A zero coordinate of any feasible allocation admits an explicitly
constructed feasible competitor with strictly higher objective. -/
theorem allocation_boundary_improvement {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (j : ι) (huj : u j = 0) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i) ≤ 1 ∧
      allocationObjective t a u < allocationObjective t a v := by
  classical
  obtain ⟨x, hx0, hx1, hs0, hs1, hgain⟩ :=
    exists_allocation_entry_gain ht (ha j) (allocationObjective_nonneg ht ha hu0)
  let s : ℝ := allocationCost t (a j) x
  let k : ℝ := 1 - s
  have hk0 : 0 ≤ k := le_of_lt (sub_pos.mpr hs1)
  have hk1 : k ≤ 1 := by dsimp only [k]; linarith
  let w : ι → ℝ := fun i => k * u i
  have hwj : w j = 0 := by simp only [w, huj, mul_zero]
  let v : ι → ℝ := Function.update w j s
  have hv0 : ∀ i, 0 ≤ v i := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [v, Function.update_self] using le_of_lt hs0
    · simpa only [v, Function.update_of_ne hij, w] using mul_nonneg hk0 (hu0 i)
  have hsumv : (∑ i, v i) = (∑ i, w i) + s := by
    have h := allocation_sum_update_add w j s
    simpa only [hwj, zero_add, v] using h
  have hsumw : (∑ i, w i) = k * ∑ i, u i := by
    dsimp only [w]
    rw [Finset.mul_sum]
  have hv1 : (∑ i, v i) ≤ 1 := by
    rw [hsumv, hsumw]
    have h := mul_le_mul_of_nonneg_left hu1 hk0
    simp only [mul_one] at h
    dsimp only [k] at h ⊢
    linarith
  have hcoordinate : allocationCoordinate t (a j) s = x :=
    allocationCoordinate_cost ht (ha j) hx0.le hx1
  have hobjv : allocationObjective t a v = allocationObjective t a w + a j * x := by
    change allocationObjective t a (Function.update w j s) = _
    rw [allocationObjective_update_zero_eq hwj, hcoordinate]
  have hscale : k * allocationObjective t a u ≤ allocationObjective t a w :=
    allocationObjective_scale_le ht ha hu0 hk0 hk1
  refine ⟨v, hv0, hv1, ?_⟩
  rw [hobjv]
  dsimp only [k] at hscale
  nlinarith only [hscale, hgain]

/-- Every actual global maximizer has strictly positive original allocations.
The proof constructs and compares a better competitor at each putative zero;
interiority is not supplied as a premise. -/
theorem allocation_maximizer_pos {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    ∀ i, 0 < u i := by
  intro j
  by_contra hj
  have huj : u j = 0 := le_antisymm (le_of_not_gt hj) (hu0 j)
  obtain ⟨v, hv0, hv1, hbetter⟩ := allocation_boundary_improvement ht ha hu0 hu1 j huj
  exact (not_lt_of_ge (hmax v hv0 hv1)) hbetter

/-- Interiority for the literal real-power maximization problem from the
manuscript, with exactly its original global maximizing property. -/
theorem manuscript_allocation_maximizer_pos {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
        ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) :
    ∀ i, 0 < u i := by
  apply allocation_maximizer_pos ht ha hu0 hu1
  intro v hv0 hv1
  rw [allocationObjective_eq_rpow ht ha hv0, allocationObjective_eq_rpow ht ha hu0]
  exact hmax v hv0 hv1

/-- An actual interior optimizer with saturated budget exists for every finite
nonempty positive mass vector and positive time. -/
theorem exists_positive_saturated_allocation_maximizer
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        allocationObjective t a v ≤ allocationObjective t a u := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_saturated_allocation_maximizer ht ha
  exact ⟨u, allocation_maximizer_pos ht ha hu0 hu1.le hmax, hu1, hmax⟩

/-- The same actual interior, full-budget optimizer existence theorem written
with the exact real-power objective of `eq:main-D`. -/
theorem exists_manuscript_positive_saturated_allocation_maximizer
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_manuscript_saturated_allocation_maximizer ht ha
  exact ⟨u, manuscript_allocation_maximizer_pos ht ha hu0 hu1.le hmax, hu1, hmax⟩

end IdentityTesting
