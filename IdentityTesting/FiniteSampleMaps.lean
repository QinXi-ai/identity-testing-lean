import IdentityTesting.FiniteKernels
import IdentityTesting.FiniteIID

/-!
# Actual whole-sample deterministic maps

Pushforward commutes with the explicit IID law. Changing a single-observation
law by a deterministic deletion of mass b changes the full n-sample law by at
most n*b, including n=0. No coupling or marginal identity is assumed.
-/

noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
open Classical

universe u v
variable {Ω : Type u} {Ξ : Type v} [Fintype Ω] [Fintype Ξ]

theorem probability_ext {p q : Probability Ω} (h : ∀ x, p.mass x = q.mass x) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

/-- The exact probability of every sample tuple after a coordinatewise map. -/
theorem mapLaw_productLaw_mass (p : Probability Ω) (f : Ω → Ξ) (n : ℕ)
    (y : Fin n → Ξ) :
    (mapLaw (productLaw p n) (fun sample => f ∘ sample)).mass y =
      (productLaw (mapLaw p f) n).mass y := by
  calc
    (mapLaw (productLaw p n) (fun sample => f ∘ sample)).mass y =
        ∑ sample : Fin n → Ω, ∏ j,
          if f (sample j) = y j then p.mass (sample j) else 0 := by
      rw [mapLaw_mass]
      apply Finset.sum_congr rfl
      intro sample _
      rw [Fintype.prod_ite_zero]
      simp only [funext_iff, Function.comp_apply, productLaw_mass]
      split_ifs <;> rfl
    _ = ∏ j, ∑ x, if f x = y j then p.mass x else 0 :=
      (Fintype.prod_sum (fun j x => if f x = y j then p.mass x else 0)).symm
    _ = (productLaw (mapLaw p f) n).mass y := by
      simp only [productLaw_mass, mapLaw_mass]

theorem mapLaw_productLaw (p : Probability Ω) (f : Ω → Ξ) (n : ℕ) :
    mapLaw (productLaw p n) (fun sample => f ∘ sample) =
      productLaw (mapLaw p f) n :=
  probability_ext (mapLaw_productLaw_mass p f n)

/-- Exact one-coordinate expectations under the actual fixed-size IID law. -/
theorem productLaw_coordinate_sum (p : Probability Ω) (n : ℕ) (j : Fin n)
    (g : Ω → ℝ) :
    (∑ sample : Fin n → Ω, (productLaw p n).mass sample * g (sample j)) =
      ∑ x, p.mass x * g x := by
  classical
  calc
    (∑ sample : Fin n → Ω, (productLaw p n).mass sample * g (sample j)) =
        ∑ sample : Fin n → Ω, ∑ x,
          (if sample j = x then (productLaw p n).mass sample else 0) * g x := by
      apply Finset.sum_congr rfl
      intro sample _
      simp [ite_mul]
    _ = ∑ x, (∑ sample : Fin n → Ω,
        if sample j = x then (productLaw p n).mass sample else 0) * g x := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp only [FiniteIID.productLaw_coordinate_mass]

/-- A union bound for the actual event that the sample tuple changes. -/
theorem productLaw_map_change_mass_le (p : Probability Ω) (f : Ω → Ω) (n : ℕ) :
    (∑ sample : Fin n → Ω,
      if f ∘ sample ≠ sample then (productLaw p n).mass sample else 0) ≤
      (n : ℝ) * ∑ x, if f x ≠ x then p.mass x else 0 := by
  classical
  calc
    (∑ sample : Fin n → Ω,
        if f ∘ sample ≠ sample then (productLaw p n).mass sample else 0) ≤
        ∑ sample : Fin n → Ω, ∑ j : Fin n,
          if f (sample j) ≠ sample j then (productLaw p n).mass sample else 0 := by
      apply Finset.sum_le_sum
      intro sample _
      by_cases h : f ∘ sample = sample
      · simp only [h, ne_eq, not_true_eq_false, ite_false]
        exact Finset.sum_nonneg fun j _ => by
          split_ifs <;> first | exact (productLaw p n).nonneg sample | exact le_rfl
      · obtain ⟨j, hj⟩ : ∃ j, f (sample j) ≠ sample j := by
          by_contra! hall
          exact h (funext hall)
        rw [if_pos h]
        calc
          (productLaw p n).mass sample =
              (if f (sample j) ≠ sample j then (productLaw p n).mass sample else 0) :=
            (if_pos hj).symm
          _ ≤ _ := by
            apply Finset.single_le_sum (f := fun i : Fin n =>
              if f (sample i) ≠ sample i then (productLaw p n).mass sample else 0)
              (s := Finset.univ) ?_ (Finset.mem_univ j)
            intro i _
            dsimp only
            split_ifs <;> first | exact (productLaw p n).nonneg sample | exact le_rfl
    _ = ∑ j : Fin n, ∑ sample : Fin n → Ω,
        (productLaw p n).mass sample * (if f (sample j) ≠ sample j then 1 else 0) := by
      rw [Finset.sum_comm]
      simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ _j : Fin n, ∑ x, if f x ≠ x then p.mass x else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [mul_ite, mul_one, mul_zero] using
        productLaw_coordinate_sum p n j (fun x => if f x ≠ x then 1 else 0)
    _ = _ := by simp

/-- Actual product-law change bound, not a bound on one-observation marginals. -/
theorem totalVariation_productLaw_mapLaw_le (p : Probability Ω) (f : Ω → Ω) (n : ℕ) :
    totalVariation (productLaw (mapLaw p f) n) (productLaw p n) ≤
      (n : ℝ) * ∑ x, if f x ≠ x then p.mass x else 0 := by
  rw [← mapLaw_productLaw]
  refine (totalVariation_mapLaw_self_le (productLaw p n) (fun sample => f ∘ sample)).trans ?_
  convert productLaw_map_change_mass_le p f n using 1
  apply Finset.sum_congr rfl
  intro sample _
  split_ifs <;> rfl

/-- Sending a finite set of labels to a chosen label costs at most n times its
reference mass, with no condition on whether the target label belongs to it. -/
theorem totalVariation_productLaw_delete_le (p : Probability Ω) (D : Finset Ω)
    (z : Ω) (n : ℕ) :
    totalVariation
      (productLaw (mapLaw p (fun x => if x ∈ D then z else x)) n)
      (productLaw p n) ≤ (n : ℝ) * ∑ x ∈ D, p.mass x := by
  refine (totalVariation_productLaw_mapLaw_le p (fun x => if x ∈ D then z else x) n).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  calc
    (∑ x, if (if x ∈ D then z else x) ≠ x then p.mass x else 0) ≤
        ∑ x, if x ∈ D then p.mass x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ D
      · simp only [hx, ite_true]
        split_ifs <;> first | exact le_rfl | exact p.nonneg x
      · simp [hx]
    _ = _ := by simp

end IdentityTesting.FiniteTesting
