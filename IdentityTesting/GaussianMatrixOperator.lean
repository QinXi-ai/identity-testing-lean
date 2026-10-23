import IdentityTesting.GaussianMatrixGeometry

/-! The Euclidean operator norm of the matrix in the Gaussian argument. -/
noncomputable section
namespace IdentityTesting.GeneralSignedMatrix

def matrixEuclideanOperator {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  M.toEuclideanLin.mkContinuous (frobeniusNorm M) (matrix_norm_le_frobenius M)

theorem matrix_operator_norm_le_frobenius {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    ‖matrixEuclideanOperator M‖ ≤ frobeniusNorm M := by
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (matrix_norm_le_frobenius M)

theorem scaled_matrix_operator_norm_le_half {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (n : ℕ) (hsmall : (n : ℝ) * frobeniusNorm M ≤ 1 / 2) :
    (n : ℝ) * ‖matrixEuclideanOperator M‖ ≤ 1 / 2 :=
  (mul_le_mul_of_nonneg_left (matrix_operator_norm_le_frobenius M)
    (Nat.cast_nonneg n)).trans hsmall

end IdentityTesting.GeneralSignedMatrix
