import IdentityTesting.AllocationStationarity
import IdentityTesting.CountableRoots
import IdentityTesting.FiniteEmbedding

/-!
# The finite allocation objective inside the original countable functional

Finite vectors are extended by zero, and arbitrary countable feasible
allocations are restricted back to their finite mass support.  Both operations
preserve the relevant objective.  Thus the countable supremum is exactly the
value of an actual finite optimizer, including at the original countable root.
No finite objective or root is redefined in this bridge.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting

/-- Zero extension of an arbitrary finite real vector, for masses as well as
allocations.  On probability masses it is the existing `extendFiniteMass`. -/
def extendFiniteVector {k : ℕ} (v : Fin k → ℝ) (n : ℕ) : ℝ :=
  if hn : n < k then v ⟨n, hn⟩ else 0

@[simp]
theorem extendFiniteVector_val {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    extendFiniteVector v i.val = v i := by
  simp [extendFiniteVector]

theorem extendFiniteVector_probability_mass {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) :
    extendFiniteVector q.mass = (extendFiniteLaw q).mass := rfl

private theorem finiteBridge_hasSum {k : ℕ} (f : ℕ → ℝ)
    (hoff : ∀ n, n ∉ Set.range (fun i : Fin k => i.val) → f n = 0) :
    HasSum f (∑ i : Fin k, f i.val) := by
  have hf : HasSum (f ∘ (fun i : Fin k => i.val)) (∑ i : Fin k, f i.val) := by
    simpa only [Function.comp_apply] using hasSum_fintype (fun i : Fin k => f i.val)
  exact (Fin.val_injective.hasSum_iff (f := f) (a := ∑ i : Fin k, f i.val) hoff).mp hf

theorem extendFiniteVector_hasSum {k : ℕ} (v : Fin k → ℝ) :
    HasSum (extendFiniteVector v) (∑ i, v i) := by
  have hoff : ∀ n, n ∉ Set.range (fun i : Fin k => i.val) → extendFiniteVector v n = 0 := by
    intro n hn
    have hnot : ¬n < k := fun h => hn ⟨⟨n, h⟩, rfl⟩
    simp only [extendFiniteVector, dif_neg hnot]
  simpa only [extendFiniteVector_val] using finiteBridge_hasSum (extendFiniteVector v) hoff

theorem extendFiniteVector_nonneg {k : ℕ} {v : Fin k → ℝ}
    (hv : ∀ i, 0 ≤ v i) : ∀ n, 0 ≤ extendFiniteVector v n := by
  intro n
  unfold extendFiniteVector
  split
  · exact hv _
  · exact le_rfl

/-- A genuinely feasible finite allocation extends to a genuinely feasible
countable allocation, including its summability obligation. -/
theorem allocationFeasible_extendFiniteVector {k : ℕ} {u : Fin k → ℝ}
    (hu : u ∈ allocationSimplex (Fin k)) : AllocationFeasible (extendFiniteVector u) := by
  refine ⟨extendFiniteVector_nonneg hu.1, (extendFiniteVector_hasSum u).summable, ?_⟩
  rw [(extendFiniteVector_hasSum u).tsum_eq]
  exact hu.2

/-- Restricting a countable feasible allocation to the finite mass support
cannot increase its total budget. -/
theorem allocationSimplex_restrict_countable {k : ℕ} {u : ℕ → ℝ}
    (hu : AllocationFeasible u) :
    (fun i : Fin k => u i.val) ∈ allocationSimplex (Fin k) := by
  refine ⟨fun i => hu.1 i.val, ?_⟩
  rw [Fin.sum_univ_eq_sum_range]
  exact (hu.2.1.sum_le_tsum (Finset.range k) (fun i _ => hu.1 i)).trans hu.2.2

/-- The countable objective with finite mass support is exactly its finite
real-power sum, even if allocations outside that support are nonzero. -/
theorem countableAllocationObjective_extendFiniteVector_eq_sum
    {k : ℕ} (a : Fin k → ℝ) (t : ℝ) (u : ℕ → ℝ) :
    countableAllocationObjective (extendFiniteVector a) t u =
      ∑ i : Fin k, a i * (u i.val / (u i.val + t ^ 2 * (a i) ^ 2)) ^ (1 / 4 : ℝ) := by
  let f : ℕ → ℝ := fun n => extendFiniteVector a n *
    (u n / (u n + t ^ 2 * (extendFiniteVector a n) ^ 2)) ^ (1 / 4 : ℝ)
  have hoff : ∀ n, n ∉ Set.range (fun i : Fin k => i.val) → f n = 0 := by
    intro n hn
    have hnot : ¬n < k := fun h => hn ⟨⟨n, h⟩, rfl⟩
    simp only [f, extendFiniteVector, dif_neg hnot, zero_mul]
  have h := (finiteBridge_hasSum f hoff).tsum_eq
  simpa only [countableAllocationObjective, f, extendFiniteVector_val] using h

/-- Objective preservation under actual countable-to-finite restriction. -/
theorem countableAllocationObjective_extendFiniteVector_eq_objective
    {k : ℕ} {a : Fin k → ℝ} {t : ℝ} {u : ℕ → ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hu : ∀ n, 0 ≤ u n) :
    countableAllocationObjective (extendFiniteVector a) t u =
      allocationObjective t a (fun i : Fin k => u i.val) := by
  rw [countableAllocationObjective_extendFiniteVector_eq_sum]
  exact (allocationObjective_eq_rpow ht ha (fun i => hu i.val)).symm

/-- Objective preservation under actual finite-to-countable extension. -/
theorem countableAllocationObjective_extendFiniteVectors
    {k : ℕ} {a u : Fin k → ℝ} {t : ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hu : ∀ i, 0 ≤ u i) :
    countableAllocationObjective (extendFiniteVector a) t (extendFiniteVector u) =
      allocationObjective t a u := by
  simpa only [extendFiniteVector_val] using
    countableAllocationObjective_extendFiniteVector_eq_objective ht ha
      (extendFiniteVector_nonneg hu)

/-- Exact attainable-value correspondence, with original countable feasibility
on one side and the existing finite simplex/objective on the other. -/
theorem allocation_finite_attainable_iff {k : ℕ} {a : Fin k → ℝ} {t : ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (d : ℝ) :
    (∃ u : ℕ → ℝ, AllocationFeasible u ∧
      d = countableAllocationObjective (extendFiniteVector a) t u) ↔
    (∃ v : Fin k → ℝ, v ∈ allocationSimplex (Fin k) ∧
      d = allocationObjective t a v) := by
  constructor
  · rintro ⟨u, hu, hvalue⟩
    refine ⟨(fun i => u i.val), allocationSimplex_restrict_countable hu, ?_⟩
    exact hvalue.trans (countableAllocationObjective_extendFiniteVector_eq_objective ht ha hu.1)
  · rintro ⟨v, hv, hvalue⟩
    refine ⟨extendFiniteVector v, allocationFeasible_extendFiniteVector hv, ?_⟩
    exact hvalue.trans (countableAllocationObjective_extendFiniteVectors ht ha hv.1).symm

/-- The actual countable supremum equals the supremum of existing finite
objective values; no new finite functional is introduced. -/
theorem allocationD_extendFiniteVector_eq_sSup {k : ℕ} {a : Fin k → ℝ} {t : ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    allocationD (extendFiniteVector a) t =
      sSup {d : ℝ | ∃ u : Fin k → ℝ, u ∈ allocationSimplex (Fin k) ∧
        d = allocationObjective t a u} := by
  unfold allocationD
  apply congrArg sSup
  ext d
  exact allocation_finite_attainable_iff ht ha d

/-- The countable functional of a zero-extended finite positive vector is the
value of any actual finite optimizer.  The finite maximizing property is over
the existing original budget simplex. -/
theorem allocationD_extendFiniteVector_eq_optimizer
    {k : ℕ} {a u : Fin k → ℝ} {t : ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hu : u ∈ allocationSimplex (Fin k))
    (hmax : ∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    allocationD (extendFiniteVector a) t = allocationObjective t a u := by
  rw [allocationD_extendFiniteVector_eq_sSup ht ha]
  have hmem : allocationObjective t a u ∈
      {d : ℝ | ∃ v : Fin k → ℝ, v ∈ allocationSimplex (Fin k) ∧
        d = allocationObjective t a v} := ⟨u, hu, rfl⟩
  have hbound : ∀ d ∈
      {d : ℝ | ∃ v : Fin k → ℝ, v ∈ allocationSimplex (Fin k) ∧
        d = allocationObjective t a v}, d ≤ allocationObjective t a u := by
    rintro d ⟨v, hv, rfl⟩
    exact hmax v hv.1 hv.2
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

/-- Specialization to the already defined extension of an actual finite
probability law; the law is not replaced by a separate extension model. -/
theorem allocationD_extendFiniteLaw_eq_optimizer
    {k : ℕ} (q : FiniteTesting.Probability (Fin k)) {t : ℝ} {u : Fin k → ℝ}
    (ht : 0 < t) (hq : ∀ i, 0 < q.mass i) (hu : u ∈ allocationSimplex (Fin k))
    (hmax : ∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t q.mass v ≤ allocationObjective t q.mass u) :
    allocationD (extendFiniteLaw q).mass t = allocationObjective t q.mass u := by
  rw [← extendFiniteVector_probability_mass q]
  exact allocationD_extendFiniteVector_eq_optimizer ht hq hu hmax

private theorem finiteBridge_nonempty {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) : Nonempty (Fin k) := by
  by_cases hk : 0 < k
  · exact ⟨⟨0, hk⟩⟩
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    have htotal := q.total
    norm_num at htotal

/-- An actual finite positive full-budget optimizer at the original countable
root has objective exactly equal to the original radius.  Positivity of the
root and nonemptiness of the finite alphabet are derived internally. -/
theorem exists_finite_allocation_optimizer_at_root
    {k : ℕ} (q : FiniteTesting.Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot (extendFiniteLaw q) e ∧
      ∃ u : Fin k → ℝ, (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
        allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass u = e ∧
        ∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
          allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass v ≤
            allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass u := by
  letI : Nonempty (Fin k) := finiteBridge_nonempty q
  have hroot := allocationRoot_spec (extendFiniteLaw q) he0 he1
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer hroot.1 hq
  have hvalue := allocationD_extendFiniteLaw_eq_optimizer q hroot.1 hq
    ⟨(fun i => (hu0 i).le), hu1.le⟩ hmax
  exact ⟨hroot.1, u, hu0, hu1, hvalue.symm.trans hroot.2, hmax⟩

/-- The actual finite optimizer at the original root also supplies its
constructed positive KKT scalar and both original budget identities. -/
theorem exists_finite_allocation_optimizer_kkt_at_root
    {k : ℕ} (q : FiniteTesting.Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot (extendFiniteLaw q) e ∧
      ∃ (u : Fin k → ℝ) (β : ℝ), (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
        allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass u = e ∧
        (∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
          allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass v ≤
            allocationObjective (allocationRoot (extendFiniteLaw q) e) q.mass u) ∧
        0 < β ∧
        (∀ i, q.mass i *
          (allocationCoordinate (allocationRoot (extendFiniteLaw q) e) (q.mass i) (u i)) ^ 3 =
            β * (1 -
              (allocationCoordinate (allocationRoot (extendFiniteLaw q) e) (q.mass i) (u i)) ^ 4) ^ 2) ∧
        1 = (allocationRoot (extendFiniteLaw q) e) ^ 2 * β * ∑ i,
          q.mass i * allocationCoordinate (allocationRoot (extendFiniteLaw q) e) (q.mass i) (u i) *
            (1 - (allocationCoordinate (allocationRoot (extendFiniteLaw q) e) (q.mass i) (u i)) ^ 4) := by
  letI : Nonempty (Fin k) := finiteBridge_nonempty q
  obtain ⟨ht, u, hu0, hu1, hvalue, hmax⟩ := exists_finite_allocation_optimizer_at_root q hq he0 he1
  obtain ⟨β, hβ, hstationary, hbudget⟩ := allocation_optimizer_kkt ht hq hu0 hu1 hmax
  exact ⟨ht, u, β, hu0, hu1, hvalue, hmax, hβ, hstationary, hbudget⟩

/-- A usable transformed-coordinate witness at the original countable root:
its displacement sum is the radius and its exact transformed budget is one.
The witness comes from an actual finite optimizer, not a supplied certificate. -/
theorem exists_finite_allocation_coordinates_at_root
    {k : ℕ} (q : FiniteTesting.Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot (extendFiniteLaw q) e ∧
      ∃ (x : Fin k → ℝ) (β : ℝ), (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i * x i) = e ∧
        (allocationRoot (extendFiniteLaw q) e) ^ 2 *
          (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1 ∧
        0 < β ∧ (∀ i, q.mass i * (x i) ^ 3 = β * (1 - (x i) ^ 4) ^ 2) ∧
        1 = (allocationRoot (extendFiniteLaw q) e) ^ 2 * β *
          ∑ i, q.mass i * x i * (1 - (x i) ^ 4) := by
  obtain ⟨ht, u, β, hu0, hu1, hvalue, hmax, hβ, hstationary, hbudget⟩ :=
    exists_finite_allocation_optimizer_kkt_at_root q hq he0 he1
  let x : Fin k → ℝ := fun i =>
    allocationCoordinate (allocationRoot (extendFiniteLaw q) e) (q.mass i) (u i)
  refine ⟨ht, x, β, ?_, hvalue, ?_, hβ, hstationary, hbudget⟩
  · intro i
    exact ⟨allocationCoordinate_pos ht (hq i) (hu0 i),
      (allocationCoordinate_range ht (hq i) (hu0 i).le).2⟩
  · exact (allocation_constructed_budget_eq Finset.univ
      (allocationRoot (extendFiniteLaw q) e) q.mass u ht
      (fun i _ => hq i) (fun i _ => (hu0 i).le)).symm.trans hu1

end IdentityTesting
