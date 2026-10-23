import IdentityTesting.FiniteEmbedding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Uniform signs and the diagonal likelihood moment bound

The uniform sign law is constructed as an actual normalized product law on
`Fin d → Bool`.  Its moment-generating function is computed exactly, and the
library's power-series proof of `cosh x ≤ exp (x²/2)` gives the moment bound.

The family of alternative laws and its diagonal one-observation likelihood
identity remain hypotheses.  This module does not construct the manuscript's
paired-displacement perturbations or prove their separation/allocation estimates.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.SignedDiagonalMoment

def sign : Bool → ℝ
  | false => -1
  | true => 1

def uniformBool : FiniteTesting.Probability Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

def uniformSigns (d : ℕ) : FiniteTesting.Probability (Fin d → Bool) :=
  FiniteTesting.productLaw uniformBool d

@[simp] theorem uniformSigns_mass_prod (d : ℕ) (σ : Fin d → Bool) :
    (uniformSigns d).mass σ = ∏ _j : Fin d, (1 / 2 : ℝ) := rfl

theorem uniformSigns_mass_eq (d : ℕ) (σ : Fin d → Bool) :
    (uniformSigns d).mass σ = (1 / 2 : ℝ) ^ d := by
  simp only [uniformSigns_mass_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem uniformSigns_mass_pos (d : ℕ) (σ : Fin d → Bool) :
    0 < (uniformSigns d).mass σ := by
  rw [uniformSigns_mass_eq]
  exact pow_pos (by norm_num) d

/-- Exact factorization for independent uniform coordinates of the constructed law. -/
theorem uniformSigns_prod_expectation {d : ℕ} (g : Fin d → Bool → ℝ) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ * ∏ j, g j (σ j)) =
      ∏ j, ∑ b : Bool, uniformBool.mass b * g j b := by
  simp only [uniformSigns, FiniteTesting.productLaw_mass]
  calc
    (∑ σ : Fin d → Bool, (∏ j, uniformBool.mass (σ j)) * ∏ j, g j (σ j)) =
        ∑ σ : Fin d → Bool, ∏ j, uniformBool.mass (σ j) * g j (σ j) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_mul_distrib]
    _ = ∏ j, ∑ b : Bool, uniformBool.mass b * g j b :=
      (Fintype.prod_sum (fun j b => uniformBool.mass b * g j b)).symm

theorem uniformBool_exp_sign (t : ℝ) :
    (∑ b : Bool, uniformBool.mass b * Real.exp (t * sign b)) = Real.cosh t := by
  simp only [Fintype.sum_bool, uniformBool, sign, mul_one, mul_neg_one]
  rw [Real.cosh_eq]
  ring

/-- Exact MGF of an actual uniform sign vector. -/
theorem uniformSigns_mgf {d : ℕ} (t : Fin d → ℝ) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (∑ j, t j * sign (σ j))) = ∏ j, Real.cosh (t j) := by
  calc
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
        Real.exp (∑ j, t j * sign (σ j))) =
        ∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
          ∏ j, Real.exp (t j * sign (σ j)) := by
      simp only [Real.exp_sum]
    _ = ∏ j, ∑ b : Bool, uniformBool.mass b * Real.exp (t j * sign b) :=
      uniformSigns_prod_expectation (fun j b => Real.exp (t j * sign b))
    _ = ∏ j, Real.cosh (t j) := by
      simp only [uniformBool_exp_sign]

def diagonalInteraction {d : ℕ} (M : Fin d → ℝ) (σ τ : Fin d → Bool) : ℝ :=
  ∑ j, M j * sign (σ j) * sign (τ j)

theorem diagonalInteraction_smul {d : ℕ} (c : ℝ) (M : Fin d → ℝ)
    (σ τ : Fin d → Bool) :
    diagonalInteraction (fun j => c * M j) σ τ = c * diagonalInteraction M σ τ := by
  unfold diagonalInteraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Independent uniform sign pairs have a product-of-cosh diagonal MGF. -/
theorem uniformSigns_pair_mgf {d : ℕ} (t : Fin d → ℝ) :
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
      (uniformSigns d).mass σ * (uniformSigns d).mass τ *
        Real.exp (diagonalInteraction t σ τ)) = ∏ j, Real.cosh (t j) := by
  unfold diagonalInteraction
  calc
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
        (uniformSigns d).mass σ * (uniformSigns d).mass τ *
          Real.exp (∑ j, t j * sign (σ j) * sign (τ j))) =
        ∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
          (∑ τ : Fin d → Bool, (uniformSigns d).mass τ *
            Real.exp (∑ j, (t j * sign (σ j)) * sign (τ j))) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
        ∏ j, Real.cosh (t j * sign (σ j)) := by
      simp only [uniformSigns_mgf]
    _ = ∑ σ : Fin d → Bool, (uniformSigns d).mass σ * ∏ j, Real.cosh (t j) := by
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      cases σ j <;> simp [sign, Real.cosh_neg]
    _ = ∏ j, Real.cosh (t j) := by
      rw [← Finset.sum_mul, (uniformSigns d).total, one_mul]

/-- This invokes Mathlib's proved power-series inequality, not an MGF hypothesis. -/
theorem cosh_le_exp_half_sq (t : ℝ) : Real.cosh t ≤ Real.exp (t ^ 2 / 2) :=
  Real.cosh_le_exp_half_sq t

theorem uniformSigns_pair_mgf_le {d : ℕ} (t : Fin d → ℝ) :
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
      (uniformSigns d).mass σ * (uniformSigns d).mass τ *
        Real.exp (diagonalInteraction t σ τ)) ≤ Real.exp (∑ j, t j ^ 2 / 2) := by
  rw [uniformSigns_pair_mgf]
  calc
    (∏ j, Real.cosh (t j)) ≤ ∏ j, Real.exp (t j ^ 2 / 2) :=
      Finset.prod_le_prod (fun j _ => (Real.cosh_pos (t j)).le)
        (fun j _ => cosh_le_exp_half_sq (t j))
    _ = Real.exp (∑ j, t j ^ 2 / 2) := (Real.exp_sum _ _).symm

variable {Ω : Type*} [Fintype Ω]

theorem likelihoodInner_nonneg (p r q : FiniteTesting.Probability Ω) :
    0 ≤ FiniteChiSquare.likelihoodInner p r q := by
  exact Finset.sum_nonneg fun x _ =>
    div_nonneg (mul_nonneg (p.nonneg x) (r.nonneg x)) (q.nonneg x)

theorem likelihoodInner_pow_le_exp {d : ℕ}
    (family : (Fin d → Bool) → FiniteTesting.Probability Ω)
    (q : FiniteTesting.Probability Ω) (M : Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, FiniteChiSquare.likelihoodInner (family σ) (family τ) q =
      1 + diagonalInteraction M σ τ) (σ τ : Fin d → Bool) :
    (FiniteChiSquare.likelihoodInner (family σ) (family τ) q) ^ n ≤
      Real.exp ((n : ℝ) * diagonalInteraction M σ τ) := by
  have hnonneg := likelihoodInner_nonneg (family σ) (family τ) q
  rw [hinner] at hnonneg ⊢
  have hexp : 1 + diagonalInteraction M σ τ ≤ Real.exp (diagonalInteraction M σ τ) := by
    linarith only [Real.add_one_le_exp (diagonalInteraction M σ τ)]
  exact (pow_le_pow_left₀ hnonneg hexp n).trans_eq
    (Real.exp_nat_mul (diagonalInteraction M σ τ) n).symm

/-- The actual finite-prior IID pair moment is bounded by the diagonal sign MGF. -/
theorem diagonal_iid_pair_moment_le_exp {d : ℕ}
    (family : (Fin d → Bool) → FiniteTesting.Probability Ω)
    (q : FiniteTesting.Probability Ω) (M : Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, FiniteChiSquare.likelihoodInner (family σ) (family τ) q =
      1 + diagonalInteraction M σ τ) :
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
      (uniformSigns d).mass σ * (uniformSigns d).mass τ *
        (FiniteChiSquare.likelihoodInner (family σ) (family τ) q) ^ n) ≤
      Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, M j ^ 2) := by
  calc
    (∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
        (uniformSigns d).mass σ * (uniformSigns d).mass τ *
          (FiniteChiSquare.likelihoodInner (family σ) (family τ) q) ^ n) ≤
        ∑ σ : Fin d → Bool, ∑ τ : Fin d → Bool,
          (uniformSigns d).mass σ * (uniformSigns d).mass τ *
            Real.exp ((n : ℝ) * diagonalInteraction M σ τ) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.sum_le_sum
      intro τ _
      exact mul_le_mul_of_nonneg_left (likelihoodInner_pow_le_exp family q M n hinner σ τ)
        (mul_nonneg ((uniformSigns d).nonneg σ) ((uniformSigns d).nonneg τ))
    _ ≤ Real.exp (∑ j, ((n : ℝ) * M j) ^ 2 / 2) := by
      simpa only [diagonalInteraction_smul] using
        (uniformSigns_pair_mgf_le (fun j => (n : ℝ) * M j))
    _ = Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, M j ^ 2) := by
      congr 1
      calc
        (∑ j, ((n : ℝ) * M j) ^ 2 / 2) = ∑ j, ((n : ℝ) ^ 2 / 2) * M j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := (Finset.mul_sum _ _ _).symm

/-- Bound for the chi-square of the actual IID mixture, using its proved moment identity. -/
theorem chiSquare_iid_mixture_le {d : ℕ}
    (family : (Fin d → Bool) → FiniteTesting.Probability Ω)
    (q : FiniteTesting.Probability Ω) (M : Fin d → ℝ) (n : ℕ)
    (hinner : ∀ σ τ, FiniteChiSquare.likelihoodInner (family σ) (family τ) q =
      1 + diagonalInteraction M σ τ) :
    FiniteChiSquare.chiSquare
      (FiniteTesting.mixture (uniformSigns d) (fun σ => FiniteTesting.productLaw (family σ) n))
      (FiniteTesting.productLaw q n) ≤ Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, M j ^ 2) - 1 := by
  have hidentity := FiniteChiSquare.one_add_chiSquare_iid_mixture (uniformSigns d) family q n
  have hmoment := diagonal_iid_pair_moment_le_exp family q M n hinner
  linarith only [hidentity, hmoment]

/-- Conditional lower bound in the original countable model.  The perturbation
family, its likelihood identity, separation, and small exponential bound are inputs. -/
theorem no_identityTest_extendFiniteLaw_of_diagonal_likelihood {k d : ℕ}
    (family : (Fin d → Bool) → FiniteTesting.Probability (Fin k))
    (q : FiniteTesting.Probability (Fin k)) (M : Fin d → ℝ) (ε : ℝ) (n : ℕ)
    (hq : ∀ x, 0 < q.mass x)
    (hinner : ∀ σ τ, FiniteChiSquare.likelihoodInner (family σ) (family τ) q =
      1 + diagonalInteraction M σ τ)
    (hseparated : ∀ σ, ε < FiniteTesting.totalVariation (family σ) q)
    (hsmall : Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, M j ^ 2) < (13 : ℝ) / 9) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  exact no_identityTest_extendFiniteLaw_of_pair_moment_lt (uniformSigns d) family q ε n hq
    (fun σ _ => hseparated σ) ((diagonal_iid_pair_moment_le_exp family q M n hinner).trans_lt hsmall)

end IdentityTesting.SignedDiagonalMoment
