import IdentityTesting.FiniteTesting
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Exact finite IID expectations and cylinder probabilities, derived from
the actual normalized `FiniteTesting.productLaw`. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteIID
open FiniteTesting

universe u
variable {Ω : Type u} [Fintype Ω]

def mean (p : Probability Ω) (f : Ω → ℝ) : ℝ := ∑ x, p.mass x * f x

theorem mean_nonneg (p : Probability Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ mean p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

theorem mean_mono (p : Probability Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    mean p f ≤ mean p g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x))

theorem mean_finset_sum {ι : Type*} (p : Probability Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    mean p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean p (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_productLaw_product (p : Probability Ω) (n : ℕ) (g : Fin n → Ω → ℝ) :
    mean (productLaw p n) (fun sample => ∏ j, g j (sample j)) =
      ∏ j, ∑ x, p.mass x * g j x := by
  classical
  unfold mean
  simp only [productLaw_mass]
  calc
    (∑ sample : Fin n → Ω, (∏ j, p.mass (sample j)) * (∏ j, g j (sample j))) =
        ∑ sample : Fin n → Ω, ∏ j, p.mass (sample j) * g j (sample j) := by
      apply Finset.sum_congr rfl
      intro sample _
      rw [Finset.prod_mul_distrib]
    _ = ∏ j, ∑ x, p.mass x * g j x :=
      (Fintype.prod_sum (fun j x => p.mass x * g j x)).symm

variable [DecidableEq Ω]

def cylinderIndicator {n : ℕ} (s : Finset (Fin n)) (b : Fin n → Ω)
    (sample : Fin n → Ω) : ℝ := if ∀ j ∈ s, sample j = b j then 1 else 0

omit [Fintype Ω] in
theorem cylinderIndicator_nonneg {n : ℕ} (s : Finset (Fin n)) (b sample : Fin n → Ω) :
    0 ≤ cylinderIndicator s b sample := by
  unfold cylinderIndicator
  split <;> norm_num

/-- Arbitrary finite coordinate cylinders have their actual IID probability. -/
theorem mean_productLaw_cylinder (p : Probability Ω) (n : ℕ)
    (s : Finset (Fin n)) (b : Fin n → Ω) :
    mean (productLaw p n) (cylinderIndicator s b) = ∏ j ∈ s, p.mass (b j) := by
  classical
  have hfun : cylinderIndicator s b = (fun sample : Fin n → Ω =>
      ∏ j, if j ∈ s then (if sample j = b j then (1 : ℝ) else 0) else 1) := by
    funext sample
    rw [Finset.prod_ite]
    simp only [Finset.filter_univ_mem, Finset.prod_const_one, mul_one,
      Finset.prod_boole, cylinderIndicator]
    split_ifs <;> rfl
  rw [hfun, mean_productLaw_product p n
    (fun j x => if j ∈ s then (if x = b j then (1 : ℝ) else 0) else 1)]
  calc
    (∏ j, ∑ x, p.mass x * (if j ∈ s then (if x = b j then (1 : ℝ) else 0) else 1)) =
        ∏ j, if j ∈ s then p.mass (b j) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ s
      · simp [hj, mul_ite]
      · simp [hj, p.total]
    _ = ∏ j ∈ s, p.mass (b j) := by simp

theorem mean_productLaw_constant_cylinder (p : Probability Ω) (n : ℕ)
    (s : Finset (Fin n)) (x : Ω) :
    mean (productLaw p n) (cylinderIndicator s (fun _ => x)) = p.mass x ^ s.card := by
  rw [mean_productLaw_cylinder]
  simp

theorem mean_productLaw_coordinate_indicator (p : Probability Ω) (n : ℕ)
    (j : Fin n) (x : Ω) :
    mean (productLaw p n) (fun sample => if sample j = x then (1 : ℝ) else 0) = p.mass x := by
  have hfun : cylinderIndicator {j} (fun _ => x) =
      (fun sample : Fin n → Ω => if sample j = x then (1 : ℝ) else 0) := by
    funext sample
    simp [cylinderIndicator]
  rw [← hfun, mean_productLaw_constant_cylinder]
  simp

/-- The actual probability mass of a fixed coordinate fiber. -/
theorem productLaw_coordinate_mass (p : Probability Ω) (n : ℕ) (j : Fin n) (x : Ω) :
    (∑ sample : Fin n → Ω, if sample j = x then (productLaw p n).mass sample else 0) = p.mass x := by
  simpa only [mean, mul_ite, mul_one, mul_zero] using
    mean_productLaw_coordinate_indicator p n j x

end IdentityTesting.FiniteIID
