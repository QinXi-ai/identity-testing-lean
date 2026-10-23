import IdentityTesting.EventCountMoments
import Mathlib.Algebra.BigOperators.Fin

/-! Exact fixed-size IID block splitting, with no independence hypothesis. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω]

def firstBlock (m n : ℕ) (sample : Fin (m + n) → Ω) : Fin m → Ω :=
  fun i => sample (Fin.castAdd n i)

def secondBlock (m n : ℕ) (sample : Fin (m + n) → Ω) : Fin n → Ω :=
  fun j => sample (Fin.natAdd m j)

def splitSampleEquiv (m n : ℕ) :
    (Fin (m + n) → Ω) ≃ ((Fin m → Ω) × (Fin n → Ω)) where
  toFun sample := (firstBlock m n sample, secondBlock m n sample)
  invFun pair := Fin.addCases pair.1 pair.2
  left_inv sample := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [firstBlock]
    · intro j
      simp [secondBlock]
  right_inv pair := by
    ext i <;> simp [firstBlock, secondBlock]

theorem productLaw_mass_blocks (p : Probability Ω) (m n : ℕ)
    (sample : Fin (m + n) → Ω) :
    (productLaw p (m + n)).mass sample =
      (productLaw p m).mass (firstBlock m n sample) *
        (productLaw p n).mass (secondBlock m n sample) := by
  exact Fin.prod_univ_add (fun i => p.mass (sample i))

theorem mean_productLaw_blocks (p : Probability Ω) (m n : ℕ)
    (f : (Fin m → Ω) → (Fin n → Ω) → ℝ) :
    mean (productLaw p (m + n)) (fun sample => f (firstBlock m n sample) (secondBlock m n sample)) =
      mean (productLaw p m) (fun left => mean (productLaw p n) (f left)) := by
  classical
  unfold mean
  calc
    _ = ∑ pair : (Fin m → Ω) × (Fin n → Ω),
        (productLaw p m).mass pair.1 * (productLaw p n).mass pair.2 * f pair.1 pair.2 := by
      apply Fintype.sum_equiv (splitSampleEquiv m n)
      intro sample
      rw [productLaw_mass_blocks]
      rfl
    _ = _ := by
      simp [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem mean_productLaw_firstBlock (p : Probability Ω) (m n : ℕ)
    (f : (Fin m → Ω) → ℝ) :
    mean (productLaw p (m + n)) (fun sample => f (firstBlock m n sample)) =
      mean (productLaw p m) f := by
  rw [mean_productLaw_blocks p m n (fun left _ => f left)]
  simp only [mean_const]

theorem mean_productLaw_block_product (p : Probability Ω) (m n : ℕ)
    (f : (Fin m → Ω) → ℝ) (g : (Fin n → Ω) → ℝ) :
    mean (productLaw p (m + n))
      (fun sample => f (firstBlock m n sample) * g (secondBlock m n sample)) =
        mean (productLaw p m) f * mean (productLaw p n) g := by
  rw [mean_productLaw_blocks p m n (fun left right => f left * g right)]
  have hinner : ∀ left, mean (productLaw p n) (fun right => f left * g right) =
      f left * mean (productLaw p n) g := by
    intro left
    simp [mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _
    ring
  simp only [hinner, mean_mul_const]

end IdentityTesting.ProfileTesting
