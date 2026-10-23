import IdentityTesting.FiniteIID
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-! Event frequencies and their actual finite IID moments. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.EventCounts
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def eventIndicator (E : Finset Ω) (x : Ω) : ℝ := if x ∈ E then 1 else 0
def eventMass (p : Probability Ω) (E : Finset Ω) : ℝ := ∑ x ∈ E, p.mass x
def eventFrequency (E : Finset Ω) (n : ℕ) (sample : Fin n → Ω) : ℝ :=
  (∑ j, eventIndicator E (sample j)) / n

theorem mean_eventIndicator (p : Probability Ω) (E : Finset Ω) :
    mean p (eventIndicator E) = eventMass p E := by
  classical
  simp [mean, eventIndicator, eventMass, mul_ite]

omit [DecidableEq Ω] in
theorem eventMass_nonneg (p : Probability Ω) (E : Finset Ω) : 0 ≤ eventMass p E :=
  Finset.sum_nonneg (fun x _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem eventMass_le_one (p : Probability Ω) (E : Finset Ω) : eventMass p E ≤ 1 := by
  rw [← p.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun x _ _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem mean_const (p : Probability Ω) (c : ℝ) : mean p (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, p.total]

omit [DecidableEq Ω] in
theorem mean_add (p : Probability Ω) (f g : Ω → ℝ) :
    mean p (fun x => f x + g x) = mean p f + mean p g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
theorem mean_sub (p : Probability Ω) (f g : Ω → ℝ) :
    mean p (fun x => f x - g x) = mean p f - mean p g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq Ω] in
theorem mean_mul_const (p : Probability Ω) (f : Ω → ℝ) (c : ℝ) :
    mean p (fun x => f x * c) = mean p f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

omit [DecidableEq Ω] in
theorem mean_div_const (p : Probability Ω) (f : Ω → ℝ) (c : ℝ) :
    mean p (fun x => f x / c) = mean p f / c := by
  simp [div_eq_mul_inv, mean_mul_const]

omit [DecidableEq Ω] in
theorem mean_productLaw_selected_product (p : Probability Ω) (n : ℕ)
    (s : Finset (Fin n)) (g : Fin n → Ω → ℝ) :
    mean (productLaw p n) (fun sample => ∏ j ∈ s, g j (sample j)) =
      ∏ j ∈ s, mean p (g j) := by
  classical
  have hfun : (fun sample : Fin n → Ω => ∏ j ∈ s, g j (sample j)) =
      (fun sample => ∏ j, if j ∈ s then g j (sample j) else 1) := by
    funext sample
    simp
  rw [hfun, mean_productLaw_product p n (fun j x => if j ∈ s then g j x else 1)]
  simp only [mul_ite, mul_one, Finset.sum_ite_irrel, p.total]
  simp [mean]

omit [DecidableEq Ω] in
theorem mean_productLaw_coordinate (p : Probability Ω) (n : ℕ)
    (j : Fin n) (g : Ω → ℝ) :
    mean (productLaw p n) (fun sample => g (sample j)) = mean p g := by
  simpa using mean_productLaw_selected_product p n {j} (fun _ => g)

omit [DecidableEq Ω] in
theorem mean_productLaw_two_coordinates (p : Probability Ω) (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (g h : Ω → ℝ) :
    mean (productLaw p n) (fun sample => g (sample i) * h (sample j)) =
      mean p g * mean p h := by
  simpa [hij, Ne.symm hij] using
    mean_productLaw_selected_product p n {i, j} (fun k => if k = i then g else h)

theorem mean_eventFrequency (p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) :
    mean (productLaw p n) (eventFrequency E n) = eventMass p E := by
  unfold eventFrequency
  rw [mean_div_const, mean_finset_sum]
  simp [mean_productLaw_coordinate, mean_eventIndicator, Nat.ne_of_gt hn]

theorem mean_centered_eventIndicator (p : Probability Ω) (E : Finset Ω) :
    mean p (fun x => eventIndicator E x - eventMass p E) = 0 := by
  rw [mean_sub, mean_const, mean_eventIndicator, sub_self]

theorem mean_centered_eventIndicator_sq (p : Probability Ω) (E : Finset Ω) :
    mean p (fun x => (eventIndicator E x - eventMass p E) ^ 2) =
      eventMass p E - eventMass p E ^ 2 := by
  have hsq : (fun x => (eventIndicator E x - eventMass p E) ^ 2) =
      (fun x => eventIndicator E x - eventIndicator E x * (2 * eventMass p E) +
        eventMass p E ^ 2) := by
    funext x
    unfold eventIndicator
    split_ifs <;> ring
  rw [hsq, mean_add, mean_sub, mean_mul_const, mean_const, mean_eventIndicator]
  ring

omit [DecidableEq Ω] in
theorem mean_centered_sum_sq (p : Probability Ω) (n : ℕ) (g : Ω → ℝ)
    (hg : mean p g = 0) :
    mean (productLaw p n) (fun sample => (∑ j, g (sample j)) ^ 2) =
      (n : ℝ) * mean p (fun x => g x ^ 2) := by
  have hfun : (fun sample : Fin n → Ω => (∑ j, g (sample j)) ^ 2) =
      (fun sample => ∑ i, ∑ j, g (sample i) * g (sample j)) := by
    funext sample
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hfun, mean_finset_sum]
  calc
    (∑ i, mean (productLaw p n) (fun sample => ∑ j, g (sample i) * g (sample j))) =
        ∑ i : Fin n, mean p (fun x => g x ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mean_finset_sum]
      rw [Finset.sum_eq_single i]
      · calc
          _ = mean (productLaw p n) (fun sample => g (sample i) ^ 2) := by
            congr 1
            funext sample
            ring
          _ = _ := mean_productLaw_coordinate p n i (fun x => g x ^ 2)
      · intro j _ hji
        rw [mean_productLaw_two_coordinates p n i j (Ne.symm hji), hg, zero_mul]
      · simp
    _ = _ := by simp

def eventFrequencyVariance (p : Probability Ω) (E : Finset Ω) (n : ℕ) : ℝ :=
  mean (productLaw p n) (fun sample => (eventFrequency E n sample - eventMass p E) ^ 2)

theorem eventFrequencyVariance_eq (p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) :
    eventFrequencyVariance p E n = (eventMass p E - eventMass p E ^ 2) / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfun : (fun sample : Fin n → Ω => (eventFrequency E n sample - eventMass p E) ^ 2) =
      (fun sample => (∑ j, (eventIndicator E (sample j) - eventMass p E)) ^ 2 / (n : ℝ) ^ 2) := by
    funext sample
    simp only [eventFrequency, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  unfold eventFrequencyVariance
  rw [hfun, mean_div_const, mean_centered_sum_sq p n _ (mean_centered_eventIndicator p E),
    mean_centered_eventIndicator_sq]
  field_simp

theorem eventFrequencyVariance_le (p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) : eventFrequencyVariance p E n ≤ eventMass p E / n := by
  rw [eventFrequencyVariance_eq p E n hn]
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (Nat.cast_nonneg n)

end IdentityTesting.EventCounts
