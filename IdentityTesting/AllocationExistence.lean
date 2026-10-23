import IdentityTesting.AllocationAlgebra
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Existence of finite allocation maximizers

For finite positive masses and positive time, the allocation objective has an
actual maximizer on the original nonnegative budget simplex.  Compactness is
proved from its coordinate bounds, and continuity is proved for the concrete
fourth-root objective.  The optimizer is then transported through the proved
allocation change of variables to the transformed optimization problem.

These existence results provide the optimizers used in the subsequent
allocation geometry and uniqueness arguments.
-/

namespace IdentityTesting

open scoped BigOperators

/-- The original finite allocation domain in `eq:main-D`. -/
def allocationSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1}

/-- The concrete finite allocation objective, with its nonnegative fourth root
represented by `allocationCoordinate`. -/
noncomputable def allocationObjective {ι : Type*} [Fintype ι]
    (t : ℝ) (a u : ι → ℝ) : ℝ :=
  ∑ i, a i * allocationCoordinate t (a i) (u i)

/-- The explicit double-square-root representation is the real power `1/4`
used in the manuscript, on every original allocation coordinate. -/
theorem allocationCoordinate_eq_rpow {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) :
    allocationCoordinate t a u =
      (u / (u + t ^ 2 * a ^ 2)) ^ (1 / (4 : ℝ)) := by
  have hc : 0 < t ^ 2 * a ^ 2 := by positivity
  have hr0 := (allocation_ratio_range hc hu).1
  rw [allocationCoordinate, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hr0]
  norm_num

/-- The finite objective agrees with the literal displayed objective in
`eq:main-D`, rather than merely with a separate root representation. -/
theorem allocationObjective_eq_rpow {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu : ∀ i, 0 ≤ u i) :
    allocationObjective t a u =
      ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  unfold allocationObjective
  apply Finset.sum_congr rfl
  intro i hi
  rw [allocationCoordinate_eq_rpow ht (ha i) (hu i)]

theorem allocationSimplex_nonempty (ι : Type*) [Fintype ι] :
    (allocationSimplex ι).Nonempty := by
  refine ⟨0, ?_⟩
  simp [allocationSimplex]

/-- The finite sum and coordinate inequalities defining the simplex are closed. -/
theorem isClosed_allocationSimplex (ι : Type*) [Fintype ι] :
    IsClosed (allocationSimplex ι) := by
  have hnonneg : IsClosed {u : ι → ℝ | ∀ i, 0 ≤ u i} := by
    have heq : {u : ι → ℝ | ∀ i, 0 ≤ u i} =
        ⋂ i, {u : ι → ℝ | 0 ≤ u i} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hbudget : IsClosed {u : ι → ℝ | (∑ i, u i) ≤ 1} := by
    apply isClosed_le _ continuous_const
    exact continuous_finset_sum Finset.univ fun i _ => continuous_apply i
  exact hnonneg.inter hbudget

/-- The simplex lies inside the compact cube `[0,1]^ι`, since a nonnegative
summand is bounded by the total allocation. -/
theorem isCompact_allocationSimplex (ι : Type*) [Fintype ι] :
    IsCompact (allocationSimplex ι) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1)).of_isClosed_subset
    (isClosed_allocationSimplex ι)
  intro u hu
  constructor
  · exact hu.1
  · intro i
    exact (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans hu.2

/-- The denominator in each actual coordinate stays positive on the simplex,
so the coordinate ratio and its two square roots are continuous there. -/
theorem continuousOn_allocationCoordinate {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) (i : ι) :
    ContinuousOn (fun u : ι → ℝ => allocationCoordinate t (a i) (u i))
      (allocationSimplex ι) := by
  have hratio : ContinuousOn
      (fun u : ι → ℝ => u i / (u i + t ^ 2 * (a i) ^ 2))
      (allocationSimplex ι) := by
    apply (continuous_apply i).continuousOn.div
      ((continuous_apply i).add continuous_const).continuousOn
    intro u hu
    have hui : 0 ≤ u i := hu.1 i
    have hai : 0 < a i := ha i
    exact ne_of_gt (by positivity)
  simpa only [allocationCoordinate] using hratio.sqrt.sqrt

/-- Continuity is established for the actual objective, rather than passed as
an additional premise to the optimizer-existence theorem. -/
theorem continuousOn_allocationObjective {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ContinuousOn (allocationObjective t a) (allocationSimplex ι) := by
  unfold allocationObjective
  apply continuousOn_finset_sum Finset.univ
  intro i hi
  exact continuousOn_const.mul (continuousOn_allocationCoordinate ht ha i)

/-- An actual maximizing original allocation exists for every finite collection
of positive masses and every positive time.  No optimizer witness, continuity
certificate, or compactness premise is supplied by the caller. -/
theorem exists_allocation_maximizer {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        allocationObjective t a v ≤ allocationObjective t a u := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_allocationSimplex ι).exists_isMaxOn
    (allocationSimplex_nonempty ι) (continuousOn_allocationObjective ht ha)
  refine ⟨u, hu.1, hu.2, ?_⟩
  intro v hv0 hv1
  exact (isMaxOn_iff.mp hmax) v ⟨hv0, hv1⟩

/-- Existence stated with exactly the real-power objective of `eq:main-D`. -/
theorem exists_manuscript_allocation_maximizer {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1 ∧
      ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ)) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_allocation_maximizer ht ha
  refine ⟨u, hu0, hu1, ?_⟩
  intro v hv0 hv1
  rw [← allocationObjective_eq_rpow ht ha hv0, ← allocationObjective_eq_rpow ht ha hu0]
  exact hmax v hv0 hv1

/-- The original and transformed optimization problems have exactly the same
attainable objective values.  Together with actual attainment, this is the
maximum-value equality asserted by `eq:allocation-x`. -/
theorem allocation_attainable_value_iff {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) (d : ℝ) :
    (∃ u : ι → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i, u i) ≤ 1 ∧
      (∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) = d) ↔
    (∃ x : ι → ℝ, (∀ i, 0 ≤ x i ∧ x i < 1) ∧
      t ^ 2 * (∑ i, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤ 1 ∧
        (∑ i, a i * x i) = d) := by
  constructor
  · rintro ⟨u, hu0, hu1, hvalue⟩
    let x : ι → ℝ := fun i => allocationCoordinate t (a i) (u i)
    have hx := (allocation_feasible_image_iff Finset.univ t a x ht
      (fun i _ => ha i)).2
      ⟨u, (fun i _ => hu0 i), hu1, (fun i _ => rfl)⟩
    refine ⟨x, (fun i => hx.1 i (Finset.mem_univ i)), hx.2, ?_⟩
    change allocationObjective t a u = d
    rw [allocationObjective_eq_rpow ht ha hu0]
    exact hvalue
  · rintro ⟨x, hx0, hx1, hvalue⟩
    obtain ⟨u, hu0, hu1, hcoordinate⟩ :=
      (allocation_feasible_image_iff Finset.univ t a x ht (fun i _ => ha i)).1
        ⟨(fun i _ => hx0 i), hx1⟩
    have hu0' : ∀ i, 0 ≤ u i := fun i => hu0 i (Finset.mem_univ i)
    refine ⟨u, hu0', hu1, ?_⟩
    rw [← allocationObjective_eq_rpow ht ha hu0']
    calc
      allocationObjective t a u = ∑ i, a i * x i := by
        unfold allocationObjective
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoordinate i hi]
      _ = d := hvalue

/-- The explicit coordinate map transports an actual original optimizer to an
actual optimizer of the transformed problem in `eq:allocation-x`. -/
theorem exists_transformed_allocation_maximizer {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ x : ι → ℝ, (∀ i, 0 ≤ x i ∧ x i < 1) ∧
      t ^ 2 * (∑ i, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤ 1 ∧
      ∀ y : ι → ℝ, (∀ i, 0 ≤ y i ∧ y i < 1) →
        t ^ 2 * (∑ i, (a i) ^ 2 * (y i) ^ 4 / (1 - (y i) ^ 4)) ≤ 1 →
          (∑ i, a i * y i) ≤ ∑ i, a i * x i := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_allocation_maximizer ht ha
  let x : ι → ℝ := fun i => allocationCoordinate t (a i) (u i)
  have hx : (∀ i, 0 ≤ x i ∧ x i < 1) ∧
      t ^ 2 * (∑ i, (a i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) ≤ 1 := by
    have hx' := (allocation_feasible_image_iff Finset.univ t a x ht
      (fun i _ => ha i)).2
      ⟨u, (fun i _ => hu0 i), hu1, (fun i _ => rfl)⟩
    simpa only [Finset.mem_univ, forall_true_left] using hx'
  refine ⟨x, hx.1, hx.2, ?_⟩
  intro y hy0 hy1
  obtain ⟨v, hv0, hv1, hvcoord⟩ :=
    (allocation_feasible_image_iff Finset.univ t a y ht (fun i _ => ha i)).1
      ⟨(fun i _ => hy0 i), hy1⟩
  have hv0' : ∀ i, 0 ≤ v i := fun i => hv0 i (Finset.mem_univ i)
  calc
    (∑ i, a i * y i) = allocationObjective t a v := by
      unfold allocationObjective
      apply Finset.sum_congr rfl
      intro i hi
      rw [hvcoord i hi]
    _ ≤ allocationObjective t a u := hmax v hv0' hv1
    _ = ∑ i, a i * x i := rfl

end IdentityTesting
