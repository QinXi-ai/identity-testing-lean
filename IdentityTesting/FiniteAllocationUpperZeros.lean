import IdentityTesting.FiniteAllocationUpper
import IdentityTesting.FiniteTestingRelabeling

/-! Actual allocation upper tests for arbitrary finite references, including
zero masses. Positive-support coordinates are extended by one at every zero
mass, which preserves the KKT equations and all weighted sums. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open Classical FiniteTesting

variable {Ω : Type*} [Fintype Ω]

def extendedPositiveCoordinate (q : Probability Ω)
    (x : Fin (Fintype.card (PositiveLabel q)) → ℝ) (i : Ω) : ℝ :=
  if hi : 0 < q.mass i then x ((Fintype.equivFin (PositiveLabel q)) ⟨i, hi⟩) else 1

theorem extendedPositiveCoordinate_enumeration (q : Probability Ω)
    (x : Fin (Fintype.card (PositiveLabel q)) → ℝ)
    (j : Fin (Fintype.card (PositiveLabel q))) :
    extendedPositiveCoordinate q x (positiveEnumeration q j) = x j := by
  simp only [extendedPositiveCoordinate, positiveEnumeration,
    dif_pos ((Fintype.equivFin (PositiveLabel q)).symm j).property]
  exact congrArg x ((Fintype.equivFin (PositiveLabel q)).apply_symm_apply j)

theorem positive_coordinate_sum (q : Probability Ω)
    (x : Fin (Fintype.card (PositiveLabel q)) → ℝ) (f : ℝ → ℝ) :
    (∑ i, q.mass i * f (extendedPositiveCoordinate q x i)) =
      ∑ j, (positiveFiniteLaw q).mass j * f (x j) := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < q.mass i)
    (fun i => q.mass i * f (extendedPositiveCoordinate q x i))
  have hz : (∑ i : {i : Ω // ¬ 0 < q.mass i},
      q.mass i.val * f (extendedPositiveCoordinate q x i.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : q.mass i.val = 0 := le_antisymm (le_of_not_gt i.property) (q.nonneg i)
    rw [hi, zero_mul]
  rw [hz, add_zero] at hs
  rw [← hs]
  have he := (Fintype.equivFin (PositiveLabel q)).sum_comp
    (fun j => (positiveFiniteLaw q).mass j * f (x j))
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [positiveFiniteLaw_mass, positiveEnumeration, Equiv.symm_apply_apply,
    extendedPositiveCoordinate, dif_pos i.property]

theorem exists_finite_allocation_coordinates_with_zeros {k : ℕ}
    (q : Probability (Fin k)) {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1) :
    0 < allocationRoot (extendFiniteLaw q) ε ∧
      ∃ (x : Fin k → ℝ) (β : ℝ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
        (∑ i, q.mass i * x i) = ε ∧ 0 < β ∧
        (∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2) ∧
        1 = allocationRoot (extendFiniteLaw q) ε ^ 2 * β *
          ∑ i, q.mass i * x i * (1 - x i ^ 4) := by
  obtain ⟨hT, x, β, hx, hradius, _, hβ, hkkt, hbudget⟩ :=
    exists_finite_allocation_coordinates_at_root (positiveFiniteLaw q)
      (positiveFiniteLaw_pos q) he0 he1
  rw [← allocationRoot_positiveFiniteLaw q ε] at hT hbudget
  let X := extendedPositiveCoordinate q x
  refine ⟨hT, X, β, ?_, ?_, hβ, ?_, ?_⟩
  · intro i
    by_cases hi : 0 < q.mass i
    · simpa only [X, extendedPositiveCoordinate, dif_pos hi] using
        And.intro (hx ((Fintype.equivFin (PositiveLabel q)) ⟨i, hi⟩)).1.le
          (hx ((Fintype.equivFin (PositiveLabel q)) ⟨i, hi⟩)).2.le
    · simp only [X, extendedPositiveCoordinate, dif_neg hi]
      norm_num
  · exact (positive_coordinate_sum q x id).trans hradius
  · intro i
    by_cases hi : 0 < q.mass i
    · have h := hkkt ((Fintype.equivFin (PositiveLabel q)) ⟨i, hi⟩)
      simpa only [positiveFiniteLaw_mass, positiveEnumeration, Equiv.symm_apply_apply,
        X, extendedPositiveCoordinate, dif_pos hi] using h
    · have hi0 : q.mass i = 0 := le_antisymm (le_of_not_gt hi) (q.nonneg i)
      simp [X, extendedPositiveCoordinate, hi0]
  · have hs := positive_coordinate_sum q x (fun y => y * (1 - y ^ 4))
    simp only [mul_assoc] at hbudget ⊢
    simpa only [X, hs] using hbudget

theorem original_root_ge_half_with_zeros {k : ℕ} (q : Probability (Fin k))
    {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    (1 : ℝ) / 2 ≤ allocationRoot (extendFiniteLaw q) ε := by
  have hmax : ∀ i, (positiveFiniteLaw q).mass i ≤ largestMass (extendFiniteLaw q) := by
    intro i
    rw [positiveFiniteLaw_mass]
    have h := largestIndex_spec (extendFiniteLaw q) (positiveEnumeration q i).val
    rw [← largestMass_eq_selected, extendFiniteLaw_mass_val] at h
    exact h
  have h := original_root_residual_bound (positiveFiniteLaw q) (positiveFiniteLaw_pos q)
    he0 he1 hmax
  rw [← allocationRoot_positiveFiniteLaw q ε] at h
  have hh := largestMass_pos (extendFiniteLaw q)
  have hT := (allocationRoot_spec (extendFiniteLaw q) he0 he1).1
  have hs : (1 : ℝ) / 2 ≤ allocationRoot (extendFiniteLaw q) ε ^ 2 := by
    have hp : ((1 : ℝ) / 2) * largestMass (extendFiniteLaw q) ≤
        allocationRoot (extendFiniteLaw q) ε ^ 2 * largestMass (extendFiniteLaw q) := by
      linarith
    exact (mul_le_mul_iff_left₀ hh).mp hp
  nlinarith

/-- Direct finite observation interface, with zero-reference labels allowed. -/
theorem finite_allocation_test_with_zeros {k : ℕ} (q : Probability (Fin k))
    {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Fin k)),
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * allocationRoot (extendFiniteLaw q) ε ∧
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      ∀ p : Probability (Fin k), ε < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3 := by
  obtain ⟨_, x, β, hx, hradius, hβ, hkkt, hbudget⟩ :=
    exists_finite_allocation_coordinates_with_zeros q he0 he1
  have hmax : ∀ i, q.mass i ≤ 2 * (1 - ε) := by
    intro i
    have h := largestIndex_spec (extendFiniteLaw q) i.val
    rw [← largestMass_eq_selected, extendFiniteLaw_mass_val] at h
    linarith
  exact finite_allocation_test_of_kkt q x (allocationRoot (extendFiniteLaw q) ε)
    β ε (original_root_ge_half_with_zeros q he0 he1 hbranch) hβ hx hkkt hbudget hradius hmax

/-- Original countable alternative model for every finite reference. -/
theorem finite_allocation_upper_bound_with_zeros {k : ℕ} (q : Probability (Fin k))
    {ε : ℝ} (he0 : 0 < ε) (he1 : ε < 1)
    (hbranch : largestMass (extendFiniteLaw q) / 2 ≤ 1 - ε) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * allocationRoot (extendFiniteLaw q) ε := by
  obtain ⟨_, x, β, hx, hradius, hβ, hkkt, hbudget⟩ :=
    exists_finite_allocation_coordinates_with_zeros q he0 he1
  let Q := pooledLaw (extendFiniteLaw q) (Finset.range k)
  let X := pooledCoordinate x
  have hTr := original_root_ge_half_with_zeros q he0 he1 hbranch
  have hX : ∀ z, 0 ≤ X z ∧ X z ≤ 1 := by
    intro z
    cases z with
    | none => norm_num [X, pooledCoordinate]
    | some i => exact hx ((rangeIndexEquiv k).symm i)
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
