import IdentityTesting.FinitePadding
import IdentityTesting.FiniteCoupling

/-! Actual independent two-stage priors and their whole-sample TV comparison. -/

noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
open Classical

universe u v z
variable {I : Type u} {J : Type v} {Ω : Type z} [Fintype I] [Fintype J] [Fintype Ω]

def productPrior (w : Probability I) (v : Probability J) : Probability (I × J) where
  mass ij := w.mass ij.1 * v.mass ij.2
  nonneg ij := mul_nonneg (w.nonneg ij.1) (v.nonneg ij.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, v.total, mul_one, w.total]

@[simp] theorem productPrior_mass (w : Probability I) (v : Probability J) (i : I) (j : J) :
    (productPrior w v).mass (i, j) = w.mass i * v.mass j := rfl

theorem productPrior_mass_pos_iff (w : Probability I) (v : Probability J) (i : I) (j : J) :
    0 < (productPrior w v).mass (i, j) ↔ 0 < w.mass i ∧ 0 < v.mass j := by
  rw [productPrior_mass]
  constructor
  · intro h
    constructor
    · by_contra hn
      have hz : w.mass i = 0 := le_antisymm (le_of_not_gt hn) (w.nonneg i)
      simp [hz] at h
    · by_contra hn
      have hz : v.mass j = 0 := le_antisymm (le_of_not_gt hn) (v.nonneg j)
      simp [hz] at h
  · rintro ⟨hi, hj⟩
    exact mul_pos hi hj

theorem mixture_productPrior (w : Probability I) (v : Probability J)
    (p : I → J → Probability Ω) :
    mixture (productPrior w v) (fun ij => p ij.1 ij.2) =
      mixture w (fun i => mixture v (p i)) := by
  apply probability_ext
  intro x
  simp only [mixture_mass, Fintype.sum_prod_type, productPrior_mass, Finset.mul_sum, mul_assoc]

/-- Conditional sample errors are averaged under the actual outer prior,
including zero-weight parameter values. -/
theorem two_stage_sample_tv_le (w : Probability I) (v : Probability J)
    (p : I → J → Probability Ω) (ν : I → Probability Ω) (q : Probability Ω)
    (n : ℕ) (η ξ : ℝ)
    (hconditional : ∀ i, 0 < w.mass i →
      totalVariation (mixture v (fun j => productLaw (p i j) n)) (productLaw (ν i) n) ≤ η)
    (hbase : totalVariation (mixture w (fun i => productLaw (ν i) n)) (productLaw q n) ≤ ξ) :
    totalVariation (mixture (productPrior w v) (fun ij => productLaw (p ij.1 ij.2) n))
      (productLaw q n) ≤ η + ξ := by
  rw [mixture_productPrior w v (fun i j => productLaw (p i j) n)]
  have hmid : totalVariation
      (mixture w (fun i => mixture v (fun j => productLaw (p i j) n)))
      (mixture w (fun i => productLaw (ν i) n)) ≤ η := by
    apply (totalVariation_mixtures_same_weights w _ _).trans
    calc
      _ ≤ ∑ i, w.mass i * η := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w.mass i = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (hconditional i (lt_of_le_of_ne (w.nonneg i) (Ne.symm hi))) (w.nonneg i)
      _ = η := by rw [← Finset.sum_mul, w.total, one_mul]
  exact (totalVariation_triangle _ _ _).trans (add_le_add hmid hbase)

end IdentityTesting.FiniteTesting
