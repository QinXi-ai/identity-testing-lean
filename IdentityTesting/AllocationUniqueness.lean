import IdentityTesting.AllocationStationarity

/-!
# Uniqueness of the actual finite allocation optimizer

The scalar marginal strictly decreases as its positive allocation increases.
Actual optimizer stationarity supplies a common marginal at every coordinate.
Two unequal common marginals would order all allocations strictly in the same
direction, contradicting their equal saturated budgets.  Equal marginals then
give equality at every coordinate.  No multiplier or stationarity hypothesis
remains in the final existence-and-uniqueness theorem.
-/

namespace IdentityTesting

open scoped BigOperators

/-- The actual weighted marginal strictly decreases on positive allocations. -/
theorem allocationMarginal_lt {t a u v : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) (huv : u < v) :
    allocationMarginal t a v < allocationMarginal t a u := by
  have hv : 0 < v := hu.trans huv
  let x : ℝ := allocationCoordinate t a u
  let y : ℝ := allocationCoordinate t a v
  have hx0 : 0 < x := allocationCoordinate_pos ht ha hu
  have hy0 : 0 < y := allocationCoordinate_pos ht ha hv
  have hx1 : x < 1 := (allocationCoordinate_range ht ha hu.le).2
  have hy1 : y < 1 := (allocationCoordinate_range ht ha hv.le).2
  have hxy : x < y := allocationCoordinate_lt ht ha hu.le huv
  have hpow4 : x ^ 4 < y ^ 4 := pow_lt_pow_left₀ hxy hx0.le (by norm_num)
  have hdx : 0 < 1 - x ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  have hdy : 0 < 1 - y ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hy0.le hy1)
  have hnum : (1 - y ^ 4) ^ 2 < (1 - x ^ 4) ^ 2 :=
    pow_lt_pow_left₀ (by linarith only [hpow4]) hdy.le (by norm_num)
  have hpow3 : x ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hx0.le hxy.le 3
  have hden : 4 * t ^ 2 * a * x ^ 3 ≤ 4 * t ^ 2 * a * y ^ 3 :=
    mul_le_mul_of_nonneg_left hpow3 (by positivity)
  have hdxy : 0 < 4 * t ^ 2 * a * x ^ 3 := by positivity
  have hdyy : 0 < 4 * t ^ 2 * a * y ^ 3 := by positivity
  change (1 - y ^ 4) ^ 2 / (4 * t ^ 2 * a * y ^ 3) <
    (1 - x ^ 4) ^ 2 / (4 * t ^ 2 * a * x ^ 3)
  calc
    (1 - y ^ 4) ^ 2 / (4 * t ^ 2 * a * y ^ 3) <
        (1 - x ^ 4) ^ 2 / (4 * t ^ 2 * a * y ^ 3) :=
      (div_lt_div_iff_of_pos_right hdyy).2 hnum
    _ ≤ (1 - x ^ 4) ^ 2 / (4 * t ^ 2 * a * x ^ 3) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hdxy hden

theorem allocationMarginal_strictAntiOn {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    StrictAntiOn (allocationMarginal t a) (Set.Ioi 0) := by
  intro u hu v hv huv
  exact allocationMarginal_lt ht ha hu huv

/-- Constant marginal profiles with the same positive total allocation cannot
have the first common marginal strictly below the second one.  The actual
optimizer caller below derives these profile hypotheses from feasible
variations and derives both budgets from global maximality. -/
theorem allocation_constant_marginal_not_lt
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t mu mv : ℝ} {a u v : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 < u i) (hv0 : ∀ i, 0 < v i)
    (husum : (∑ i, u i) = 1) (hvsum : (∑ i, v i) = 1)
    (huMarginal : ∀ i, allocationMarginal t (a i) (u i) = mu)
    (hvMarginal : ∀ i, allocationMarginal t (a i) (v i) = mv) :
    ¬mu < mv := by
  intro hlt
  have hcoord : ∀ i, v i < u i := by
    intro i
    by_contra hnot
    have hle : u i ≤ v i := le_of_not_gt hnot
    have hm := (allocationMarginal_strictAntiOn ht (ha i)).antitoneOn
      (hu0 i) (hv0 i) hle
    rw [huMarginal i, hvMarginal i] at hm
    exact (not_le_of_gt hlt) hm
  have hsumlt : (∑ i, v i) < ∑ i, u i :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hcoord i)
  linarith only [husum, hvsum, hsumlt]

/-- Any two actual global optimizers of the original nonnegative budget
problem coincide.  Interiority, saturation, and common marginals are all
derived inside the proof from their global maximizing properties. -/
theorem allocation_maximizers_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u v : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmaxu : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      allocationObjective t a w ≤ allocationObjective t a u)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : (∑ i, v i) ≤ 1)
    (hmaxv : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      allocationObjective t a w ≤ allocationObjective t a v) : u = v := by
  classical
  have huPos := allocation_maximizer_pos ht ha hu0 hu1 hmaxu
  have hvPos := allocation_maximizer_pos ht ha hv0 hv1 hmaxv
  have huSum := allocation_maximizer_saturated ht ha hu0 hu1 hmaxu
  have hvSum := allocation_maximizer_saturated ht ha hv0 hv1 hmaxv
  let j : ι := Classical.choice (inferInstance : Nonempty ι)
  let mu : ℝ := allocationMarginal t (a j) (u j)
  let mv : ℝ := allocationMarginal t (a j) (v j)
  have huMarginal : ∀ i, allocationMarginal t (a i) (u i) = mu := by
    intro i
    exact allocation_maximizer_marginals_eq ht ha huPos hu1 hmaxu i j
  have hvMarginal : ∀ i, allocationMarginal t (a i) (v i) = mv := by
    intro i
    exact allocation_maximizer_marginals_eq ht ha hvPos hv1 hmaxv i j
  have hnotuv : ¬mu < mv := allocation_constant_marginal_not_lt ht ha huPos hvPos
    huSum hvSum huMarginal hvMarginal
  have hnotvu : ¬mv < mu := allocation_constant_marginal_not_lt ht ha hvPos huPos
    hvSum huSum hvMarginal huMarginal
  have heq : mu = mv := le_antisymm (le_of_not_gt hnotvu) (le_of_not_gt hnotuv)
  funext i
  apply (allocationMarginal_strictAntiOn ht (ha i)).injOn (huPos i) (hvPos i)
  rw [huMarginal i, hvMarginal i, heq]

/-- Uniqueness with the exact real-power objective of the manuscript and the
original nonnegative budget constraints. -/
theorem manuscript_allocation_maximizers_unique
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u v : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmaxu : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      (∑ i, a i * (w i / (w i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
        ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)))
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : (∑ i, v i) ≤ 1)
    (hmaxv : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) ≤ 1 →
      (∑ i, a i * (w i / (w i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
        ∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) : u = v := by
  refine allocation_maximizers_unique ht ha hu0 hu1 ?_ hv0 hv1 ?_
  · intro w hw0 hw1
    rw [allocationObjective_eq_rpow ht ha hw0, allocationObjective_eq_rpow ht ha hu0]
    exact hmaxu w hw0 hw1
  · intro w hw0 hw1
    rw [allocationObjective_eq_rpow ht ha hw0, allocationObjective_eq_rpow ht ha hv0]
    exact hmaxv w hw0 hw1

/-- The original finite allocation problem has exactly one feasible global
maximizer, with no multiplier, compactness, or stationarity premise. -/
theorem exists_unique_manuscript_allocation_maximizer
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃! u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_manuscript_allocation_maximizer ht ha
  refine ⟨u, ⟨hu0, hu1, hmax⟩, ?_⟩
  intro v hv
  exact manuscript_allocation_maximizers_unique ht ha hv.1 hv.2.1 hv.2.2 hu0 hu1 hmax

/-- The unique actual optimizer is strictly positive and spends the full
budget, as asserted by the optimizer portion of `lem:allocation`. -/
theorem exists_unique_manuscript_positive_saturated_allocation_maximizer
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃! u : ι → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_manuscript_positive_saturated_allocation_maximizer ht ha
  refine ⟨u, ⟨hu0, hu1, hmax⟩, ?_⟩
  intro v hv
  exact manuscript_allocation_maximizers_unique ht ha (fun i => (hv.1 i).le)
    hv.2.1.le hv.2.2 (fun i => (hu0 i).le) hu1.le hmax

/-- A single combined result supplies the unique positive full-budget original
optimizer and an actually constructed positive KKT scalar satisfying both
manuscript equations. -/
theorem exists_unique_manuscript_allocation_optimizer_kkt
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃! u : ι → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      (∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ∧
      ∃ β : ℝ, 0 < β ∧
        (∀ i, a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
          β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2) ∧
        1 = t ^ 2 * β * ∑ i,
          a i * allocationCoordinate t (a i) (u i) *
            (1 - (allocationCoordinate t (a i) (u i)) ^ 4) := by
  obtain ⟨u, β, hu0, hu1, hmax, hβ, hstationary, hbudget⟩ :=
    exists_manuscript_allocation_optimizer_kkt ht ha
  refine ⟨u, ⟨hu0, hu1, hmax, β, hβ, hstationary, hbudget⟩, ?_⟩
  intro v hv
  exact manuscript_allocation_maximizers_unique ht ha (fun i => (hv.1 i).le)
    hv.2.1.le hv.2.2.1 (fun i => (hu0 i).le) hu1.le hmax

end IdentityTesting
