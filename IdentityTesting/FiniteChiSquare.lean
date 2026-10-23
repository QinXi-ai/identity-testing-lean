import IdentityTesting.FiniteTesting

/-!
# Exact finite likelihood second moments

This module expands the actual finite mixtures and IID product laws defined in
`FiniteTesting`.  The second-moment identities are algebraic and do not need a
positivity assumption on the reference law.  The interpretation as a chi-square
divergence and the TV bound below use a strictly positive reference law.
-/

noncomputable section

namespace IdentityTesting.FiniteChiSquare

open scoped BigOperators
open IdentityTesting.FiniteTesting

universe u v w

variable {Ω : Type u} [Fintype Ω]

/-- The reference-weighted inner product of two finite likelihood ratios. -/
def likelihoodInner (p r q : Probability Ω) : ℝ :=
  ∑ x, p.mass x * r.mass x / q.mass x

/-- The algebraic second moment minus one.  For positive `q`, the centered
sum representation proved below makes this the chi-square divergence. -/
def chiSquare (p q : Probability Ω) : ℝ :=
  likelihoodInner p p q - 1

/-- Exact factorization of the likelihood inner product for fixed-size IID laws. -/
theorem likelihoodInner_productLaw (p r q : Probability Ω) (n : ℕ) :
    likelihoodInner (productLaw p n) (productLaw r n) (productLaw q n) =
      (likelihoodInner p r q) ^ n := by
  unfold likelihoodInner
  simp only [productLaw_mass]
  calc
    (∑ sample : Fin n → Ω,
        (∏ j, p.mass (sample j)) * (∏ j, r.mass (sample j)) /
          (∏ j, q.mass (sample j))) =
        ∑ sample : Fin n → Ω, ∏ j,
          p.mass (sample j) * r.mass (sample j) / q.mass (sample j) := by
      apply Finset.sum_congr rfl
      intro sample _
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    _ = (∑ x, p.mass x * r.mass x / q.mass x) ^ n :=
      (Fintype.sum_pow (fun x => p.mass x * r.mass x / q.mass x) n).symm

variable {I : Type v} [Fintype I] {J : Type w} [Fintype J]

/-- Bilinearity for two actual finite mixtures, including nonuniform priors. -/
theorem likelihoodInner_mixtures (weightsP : Probability I)
    (familyP : I → Probability Ω) (weightsR : Probability J)
    (familyR : J → Probability Ω) (q : Probability Ω) :
    likelihoodInner (mixture weightsP familyP) (mixture weightsR familyR) q =
      ∑ i, ∑ j, weightsP.mass i * weightsR.mass j *
        likelihoodInner (familyP i) (familyR j) q := by
  unfold likelihoodInner
  simp only [mixture_mass]
  calc
    (∑ x, (∑ i, weightsP.mass i * (familyP i).mass x) *
        (∑ j, weightsR.mass j * (familyR j).mass x) / q.mass x) =
        ∑ x, ∑ i, ∑ j, (weightsP.mass i * weightsR.mass j) *
          ((familyP i).mass x * (familyR j).mass x / q.mass x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Fintype.sum_mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ j, ∑ x, (weightsP.mass i * weightsR.mass j) *
        ((familyP i).mass x * (familyR j).mass x / q.mass x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, weightsP.mass i * weightsR.mass j *
        (∑ x, (familyP i).mass x * (familyR j).mass x / q.mass x) := by
      simp only [Finset.mul_sum]

theorem likelihoodInner_mixture (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) :
    likelihoodInner (mixture weights family) (mixture weights family) q =
      ∑ i, ∑ j, weights.mass i * weights.mass j *
        likelihoodInner (family i) (family j) q :=
  likelihoodInner_mixtures weights family weights family q

/-- The actual fixed-size mixture likelihood identity used before a moment bound. -/
theorem likelihoodInner_iid_mixture (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) (n : ℕ) :
    likelihoodInner (mixture weights (fun i => productLaw (family i) n))
        (mixture weights (fun i => productLaw (family i) n)) (productLaw q n) =
      ∑ i, ∑ j, weights.mass i * weights.mass j *
        (likelihoodInner (family i) (family j) q) ^ n := by
  rw [likelihoodInner_mixture]
  simp only [likelihoodInner_productLaw]

theorem one_add_chiSquare_iid_mixture (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) (n : ℕ) :
    1 + chiSquare (mixture weights (fun i => productLaw (family i) n))
        (productLaw q n) =
      ∑ i, ∑ j, weights.mass i * weights.mass j *
        (likelihoodInner (family i) (family j) q) ^ n := by
  unfold chiSquare
  rw [likelihoodInner_iid_mixture]
  ring

/-- Normalization converts the second moment minus one into the centered sum. -/
theorem chiSquare_eq_sum_sq_div (p q : Probability Ω)
    (hq : ∀ x, 0 < q.mass x) :
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
      symm
      apply (div_eq_iff (ne_of_gt (hq x))).mpr
      rw [add_mul, sub_mul, div_mul_cancel₀ _ (ne_of_gt (hq x))]
      ring

theorem chiSquare_nonneg (p q : Probability Ω) (hq : ∀ x, 0 < q.mass x) :
    0 ≤ chiSquare p q := by
  rw [chiSquare_eq_sum_sq_div p q hq]
  exact Finset.sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (q.nonneg x)

/-- Cauchy-Schwarz gives TV squared at most one quarter of chi-square. -/
theorem totalVariation_sq_le_chiSquare_div_four (p q : Probability Ω)
    (hq : ∀ x, 0 < q.mass x) :
    (totalVariation p q) ^ 2 ≤ chiSquare p q / 4 := by
  have hCS := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset Ω)
    (fun x => |p.mass x - q.mass x|) (g := q.mass) (fun x _ => hq x)
  simp only [q.total, div_one, sq_abs] at hCS
  rw [← chiSquare_eq_sum_sq_div p q hq] at hCS
  unfold totalVariation
  nlinarith only [hCS]

end IdentityTesting.FiniteChiSquare
