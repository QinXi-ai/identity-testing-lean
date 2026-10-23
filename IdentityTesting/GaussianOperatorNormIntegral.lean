import IdentityTesting.GaussianSpectralIntegral
import IdentityTesting.GaussianMatrixOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Finiteness of the actual Gaussian squared-matrix-norm integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem gaussian_operator_norm_integrable {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ)
    (hsmall : t ^ 2 * ‖A‖ ^ 2 < 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (t ^ 2 * ‖A x‖ ^ 2 / 2))
      (standardGaussianVector (Fin d)) := by
  let T := t ^ 2 • (A.adjoint.comp A)
  have hT : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ ((t ^ 2) • A.adjoint (A x)) y =
      inner ℝ x ((t ^ 2) • A.adjoint (A y))
    rw [real_inner_smul_left, real_inner_smul_right,
      A.adjoint_inner_left, A.adjoint_inner_right]
  have hn : ‖T‖ < 1 := by
    dsimp [T]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t),
      ContinuousLinearMap.norm_adjoint_comp_self]
    nlinarith only [hsmall]
  have h := gaussian_selfadjoint_integrable T hT hn
  have he (x : EuclideanSpace ℝ (Fin d)) : inner ℝ x (T x) = t ^ 2 * ‖A x‖ ^ 2 := by
    change inner ℝ x ((t ^ 2) • A.adjoint (A x)) = _
    rw [real_inner_smul_right, A.adjoint_inner_right, real_inner_self_eq_norm_sq]
  simpa only [he] using h

theorem gaussian_matrix_norm_integrable_of_frobenius {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (t ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2))
      (standardGaussianVector (Fin d)) := by
  apply gaussian_operator_norm_integrable (matrixEuclideanOperator M) t
  have hs := pow_le_pow_left₀ (norm_nonneg (matrixEuclideanOperator M))
    (matrix_operator_norm_le_frobenius M) 2
  rw [frobeniusNorm_sq] at hs
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  linarith

end IdentityTesting.GeneralSignedMatrix
