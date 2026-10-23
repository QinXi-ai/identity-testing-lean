import IdentityTesting.GeneralSignedMatrixMoment

/-! The manuscript's signed-likelihood TV estimate for actual finite mixtures.
Reference zero masses are permitted, with the original support condition. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedMoment SignedDiagonalMoment
open FiniteTesting FiniteChiSquare

variable {Ω : Type*} [Fintype Ω]

theorem chiSquare_eq_sum_sq_div_of_support (p q : Probability Ω)
    (hsupport : ∀ x, q.mass x = 0 → p.mass x = 0) :
    chiSquare p q = ∑ x, (p.mass x - q.mass x) ^ 2 / q.mass x := by
  calc
    chiSquare p q = (∑ x, p.mass x * p.mass x / q.mass x) - 1 := rfl
    _ = ∑ x, (p.mass x * p.mass x / q.mass x - 2 * p.mass x + q.mass x) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, p.total, q.total]
      ring
    _ = ∑ x, (p.mass x - q.mass x) ^ 2 / q.mass x := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : q.mass x = 0
      · simp [hx, hsupport x hx]
      · field_simp
        ring

theorem totalVariation_sq_le_chiSquare_div_four_of_support (p q : Probability Ω)
    (hsupport : ∀ x, q.mass x = 0 → p.mass x = 0) :
    FiniteTesting.totalVariation p q ^ 2 ≤ chiSquare p q / 4 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.univ : Finset Ω) (r := fun x => |p.mass x - q.mass x|)
    (f := q.mass) (g := fun x => (p.mass x - q.mass x) ^ 2 / q.mass x)
    (fun x _ => q.nonneg x)
    (fun x _ => div_nonneg (sq_nonneg _) (q.nonneg x)) (by
      intro x _
      rw [sq_abs]
      by_cases hx : q.mass x = 0
      · simp [hx, hsupport x hx]
      · field_simp)
  rw [q.total, one_mul, ← chiSquare_eq_sum_sq_div_of_support p q hsupport] at h
  unfold FiniteTesting.totalVariation
  nlinarith only [h]

theorem productLaw_support (p q : Probability Ω)
    (hsupport : ∀ x, q.mass x = 0 → p.mass x = 0) (n : ℕ) :
    ∀ sample, (productLaw q n).mass sample = 0 → (productLaw p n).mass sample = 0 := by
  classical
  intro sample hq
  rw [productLaw_mass] at hq ⊢
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.mp hq
  exact Finset.prod_eq_zero hj (hsupport _ hz)

theorem signed_iid_mixture_support {d : ℕ}
    (family : (Fin d → Bool) → Probability Ω) (q : Probability Ω)
    (hsupport : ∀ σ x, q.mass x = 0 → (family σ).mass x = 0) (n : ℕ) :
    ∀ sample, (productLaw q n).mass sample = 0 →
      (mixture (uniformSigns d) (fun σ => productLaw (family σ) n)).mass sample = 0 := by
  intro sample hq
  rw [mixture_mass]
  apply Finset.sum_eq_zero
  intro σ _
  rw [productLaw_support (family σ) q (hsupport σ) n sample hq, mul_zero]

theorem matrix_likelihoodInner_pow_le_exp {d : ℕ}
    (family : (Fin d → Bool) → Probability Ω) (q : Probability Ω)
    (M : Fin d → Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, likelihoodInner (family σ) (family τ) q =
      1 + matrixInteraction M σ τ) (σ τ : Fin d → Bool) :
    likelihoodInner (family σ) (family τ) q ^ n ≤
      Real.exp ((n : ℝ) * matrixInteraction M σ τ) := by
  have hnonneg := likelihoodInner_nonneg (family σ) (family τ) q
  rw [hinner] at hnonneg ⊢
  have he : 1 + matrixInteraction M σ τ ≤ Real.exp (matrixInteraction M σ τ) := by
    linarith only [Real.add_one_le_exp (matrixInteraction M σ τ)]
  exact (pow_le_pow_left₀ hnonneg he n).trans_eq
    (Real.exp_nat_mul (matrixInteraction M σ τ) n).symm

/-- Actual IID-mixture second moment, with its matrix MGF derived internally. -/
theorem matrix_iid_pair_moment_le_exp {d : ℕ}
    (family : (Fin d → Bool) → Probability Ω) (q : Probability Ω)
    (M : Fin d → Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, likelihoodInner (family σ) (family τ) q =
      1 + matrixInteraction M σ τ)
    (hsmall : (n : ℝ) ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
      (uniformSigns d).mass σ * (uniformSigns d).mass τ *
        likelihoodInner (family σ) (family τ) q ^ n) ≤
      Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) := by
  calc
    _ ≤ pairExp (fun σ τ => (n : ℝ) * matrixInteraction M σ τ) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.sum_le_sum
      intro τ _
      exact mul_le_mul_of_nonneg_left (matrix_likelihoodInner_pow_le_exp family q M n hinner σ τ)
        (mul_nonneg ((uniformSigns d).nonneg σ) ((uniformSigns d).nonneg τ))
    _ ≤ _ := matrix_pair_mgf_le_exp M n hsmall

theorem matrix_chiSquare_iid_mixture_le {d : ℕ}
    (family : (Fin d → Bool) → Probability Ω) (q : Probability Ω)
    (M : Fin d → Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, likelihoodInner (family σ) (family τ) q =
      1 + matrixInteraction M σ τ)
    (hsmall : (n : ℝ) ^ 2 * frobeniusSq M ≤ 1 / 2) :
    chiSquare (mixture (uniformSigns d) (fun σ => productLaw (family σ) n)) (productLaw q n) ≤
      Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) - 1 := by
  have hi := one_add_chiSquare_iid_mixture (uniformSigns d) family q n
  have hm := matrix_iid_pair_moment_le_exp family q M n hinner hsmall
  linarith

/-- `lem:signedmatrix` / `eq:signed-tv`, including zero masses outside the
reference support and n=0. This is stronger than the symmetric-matrix statement:
the bound holds for every real matrix with the given likelihood identity. -/
theorem signed_likelihood_matrix_totalVariation {d : ℕ}
    (family : (Fin d → Bool) → Probability Ω) (q : Probability Ω)
    (M : Fin d → Fin d → ℝ) (n : ℕ)
    (hsupport : ∀ σ x, q.mass x = 0 → (family σ).mass x = 0)
    (hinner : ∀ σ τ, likelihoodInner (family σ) (family τ) q =
      1 + matrixInteraction M σ τ)
    (hsmall : (n : ℝ) * frobeniusNorm M ≤ 1 / 2) :
    FiniteTesting.totalVariation (mixture (uniformSigns d) (fun σ => productLaw (family σ) n))
      (productLaw q n) ≤ (1 / 2 : ℝ) *
        Real.sqrt (Real.exp ((n : ℝ) ^ 2 * frobeniusNorm M ^ 2) - 1) := by
  have hnonneg : 0 ≤ (n : ℝ) * frobeniusNorm M :=
    mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hnonneg hsmall 2
  rw [mul_pow, frobeniusNorm_sq] at hsq
  norm_num at hsq
  have hm := matrix_chiSquare_iid_mixture_le family q M n hinner
    (show (n : ℝ) ^ 2 * frobeniusSq M ≤ 1 / 2 by linarith)
  have htv := totalVariation_sq_le_chiSquare_div_four_of_support
    (mixture (uniformSigns d) (fun σ => productLaw (family σ) n)) (productLaw q n)
    (signed_iid_mixture_support family q hsupport n)
  rw [frobeniusNorm_sq]
  have he0 : 0 ≤ Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) - 1 := by
    have h := Real.one_le_exp_iff.mpr (mul_nonneg (sq_nonneg (n : ℝ)) (frobeniusSq_nonneg M))
    linarith
  have hs := Real.sq_sqrt he0
  have hs0 := Real.sqrt_nonneg (Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) - 1)
  nlinarith

end IdentityTesting.GeneralSignedMatrix
