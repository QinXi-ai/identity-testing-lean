import IdentityTesting.FiniteAllocationUpperAssembly
import IdentityTesting.PoolingTests

/-! Original-model finite allocation upper bound. The optimizer is obtained
from the original allocationRoot and lifted to the actual pooled observation
alphabet, including its zero-reference exterior cell. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting

def rangeIndexEquiv (k : ℕ) : Fin k ≃ {i : ℕ // i ∈ Finset.range k} where
  toFun i := ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  invFun i := ⟨i.val, Finset.mem_range.mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pooledCoordinate {k : ℕ} (x : Fin k → ℝ) : PoolLabel (Finset.range k) → ℝ
  | none => 1
  | some i => x ((rangeIndexEquiv k).symm i)

theorem finite_reference_residual_zero {k : ℕ} (q : Probability (Fin k)) :
    residualMass (extendFiniteLaw q) (Finset.range k) = 0 := by
  have hf : (fun i : {i : ℕ // i ∉ Finset.range k} => (extendFiniteLaw q).mass i.val) =
      (fun _ => (0 : ℝ)) := by
    funext i
    exact extendFiniteLaw_mass_of_not_lt q i.val
      (fun h => i.property (Finset.mem_range.mpr h))
  unfold residualMass
  rw [hf]
  simp

theorem finite_pooled_mass_none {k : ℕ} (q : Probability (Fin k)) :
    (pooledLaw (extendFiniteLaw q) (Finset.range k)).mass none = 0 :=
  finite_reference_residual_zero q

theorem finite_pooled_mass_some {k : ℕ} (q : Probability (Fin k))
    (i : {i : ℕ // i ∈ Finset.range k}) :
    (pooledLaw (extendFiniteLaw q) (Finset.range k)).mass (some i) =
      q.mass ((rangeIndexEquiv k).symm i) := by
  exact extendFiniteLaw_mass_val q ((rangeIndexEquiv k).symm i)

theorem finite_pooled_coordinate_sum {k : ℕ} (q : Probability (Fin k))
    (x : Fin k → ℝ) (f : ℝ → ℝ) :
    (∑ z : PoolLabel (Finset.range k),
      (pooledLaw (extendFiniteLaw q) (Finset.range k)).mass z * f (pooledCoordinate x z)) =
        ∑ i, q.mass i * f (x i) := by
  rw [Fintype.sum_option, finite_pooled_mass_none, zero_mul, zero_add]
  simp only [finite_pooled_mass_some, pooledCoordinate]
  exact (rangeIndexEquiv k).symm.sum_comp (fun i => q.mass i * f (x i))

/-- Every test, all finite IID moments, and the KKT coordinates are constructed
inside the proof; the radius and root are the original countable definitions. -/
theorem finite_allocation_upper_bound {k : ℕ} (q : Probability (Fin k))
    (hq : ∀ i, 0 < q.mass i) {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * allocationRoot (extendFiniteLaw q) ε := by
  obtain ⟨hT, x, β, hx, hradius, hcost, hβ, hkkt, hbudget⟩ :=
    exists_finite_allocation_coordinates_at_root q hq he0 he1
  let Q := pooledLaw (extendFiniteLaw q) (Finset.range k)
  let X := pooledCoordinate x
  have hTr := original_root_ge_half q hq he0 he1 hbranch
  have hX : ∀ z, 0 ≤ X z ∧ X z ≤ 1 := by
    intro z
    cases z with
    | none => norm_num [X, pooledCoordinate]
    | some i => exact ⟨(hx ((rangeIndexEquiv k).symm i)).1.le, (hx ((rangeIndexEquiv k).symm i)).2.le⟩
  have hkktQ : ∀ z, Q.mass z * X z ^ 3 = β * (1 - X z ^ 4) ^ 2 := by
    intro z
    cases z with
    | none => simp [Q, X, finite_pooled_mass_none, pooledCoordinate]
    | some i => simpa only [Q, X, finite_pooled_mass_some, pooledCoordinate] using hkkt ((rangeIndexEquiv k).symm i)
  have hrQ : (∑ z, Q.mass z * X z) = ε := by
    exact (finite_pooled_coordinate_sum q x id).trans hradius
  have hbQ : 1 = allocationRoot (extendFiniteLaw q) ε ^ 2 * β *
      ∑ z, Q.mass z * X z * (1 - X z ^ 4) := by
    have hs := finite_pooled_coordinate_sum q x (fun y => y * (1 - y ^ 4))
    simp only [mul_assoc] at hbudget ⊢
    simpa only [Q, X, hs] using hbudget
  have hmax : ∀ z, Q.mass z ≤ 2 * (1 - ε) := by
    intro z
    cases z with
    | none => rw [show Q.mass none = 0 from finite_pooled_mass_none q]; linarith
    | some i =>
        have h := largestIndex_spec (extendFiniteLaw q) i.val
        rw [← largestMass_eq_selected] at h
        change (extendFiniteLaw q).mass i.val ≤ 2 * (1 - ε)
        linarith
  obtain ⟨n, test, hn, hnull, halt⟩ := finite_allocation_test_of_kkt Q X
    (allocationRoot (extendFiniteLaw q) ε) β ε hTr hβ hX hkktQ hbQ hrQ hmax
  refine ⟨n, ?_, hn⟩
  apply hasIdentityTest_of_pooled_test (extendFiniteLaw q) (Finset.range k) ε n test hnull
  rw [finite_reference_residual_zero, sub_zero]
  exact halt

end IdentityTesting.FiniteAllocationUpper
