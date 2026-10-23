import IdentityTesting.AllocationUniqueness
import Mathlib.Analysis.Convex.Deriv

/-! Strict concavity of the original objective, including the simplex boundary. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocationSummand_strictConcaveOn {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun u => a * allocationCoordinate t a u) := by
  have hc : ContinuousOn (fun u => a * allocationCoordinate t a u) (Set.Ici 0) := by
    apply continuousOn_const.mul
    unfold allocationCoordinate
    apply ContinuousOn.sqrt
    apply ContinuousOn.sqrt
    apply continuousOn_id.div (continuousOn_id.add continuousOn_const)
    intro u hu
    exact ne_of_gt (add_pos_of_nonneg_of_pos hu (by positivity))
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici (0 : ℝ)) hc
  rw [interior_Ici]
  intro u hu v hv huv
  rw [(hasDerivAt_allocationSummand ht ha hu).deriv,
    (hasDerivAt_allocationSummand ht ha hv).deriv]
  exact allocationMarginal_strictAntiOn ht ha hu hv huv

theorem convex_allocationSimplex (ι : Type*) [Fintype ι] :
    Convex ℝ (allocationSimplex ι) := by
  intro u hu v hv α β hα hβ hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg hα (hu.1 i)) (mul_nonneg hβ (hv.1 i))
  · change (∑ i, (α * u i + β * v i)) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hu.2 hα, mul_le_mul_of_nonneg_left hv.2 hβ]

theorem allocationObjective_strictConcaveOn {ι : Type*} [Fintype ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    StrictConcaveOn ℝ (allocationSimplex ι) (allocationObjective t a) := by
  classical
  refine ⟨convex_allocationSimplex ι, ?_⟩
  intro u hu v hv huv α β hα hβ hab
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ v j := by
    by_contra h
    apply huv
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  have hle (i : ι) := (allocationSummand_strictConcaveOn ht (ha i)).concaveOn.2
    (hu.1 i) (hv.1 i) hα.le hβ.le hab
  have hlt := (allocationSummand_strictConcaveOn ht (ha j)).2
    (hu.1 j) (hv.1 j) hj hα hβ hab
  simp only [allocationObjective, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    exact hle i
  · exact ⟨j, Finset.mem_univ j, hlt⟩

end IdentityTesting
