import IdentityTesting.GaussianVectorInvariant
import IdentityTesting.GeneralSignedMatrixMoment
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Gram forms and the Frobenius bound for the actual Gaussian matrix input. -/
noncomputable section
open scoped BigOperators Matrix
namespace IdentityTesting.GeneralSignedMatrix

theorem gram_quadratic_eq_norm_sq {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x ((t ^ 2 • (Mᴴ * M)).toEuclideanLin x) =
      t ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 := by
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanLin_apply]
  simp only [star_trivial]
  rw [
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  congr 1
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanLin_apply, star_trivial] using
    (real_inner_self_eq_norm_sq (M.toEuclideanLin x))

theorem gram_trace_eq_frobenius {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    (t ^ 2 • (Mᴴ * M)).trace = t ^ 2 * frobeniusSq M := by
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial, frobeniusSq, rowSquareSum, sq]
  rw [Finset.sum_comm]

theorem matrix_norm_le_frobenius {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖M.toEuclideanLin x‖ ≤ frobeniusNorm M * ‖x‖ := by
  have hsq : ‖M.toEuclideanLin x‖ ^ 2 ≤ frobeniusSq M * ‖x‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ), Real.norm_eq_abs, sq_abs,
      Matrix.toEuclideanLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct]
    calc
      _ ≤ ∑ i, (∑ j, M i j ^ 2) * ∑ j, x j ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) (fun j => x j))
      _ = _ := by rw [← Finset.sum_mul]; rfl
  have hf := frobeniusNorm_sq M
  have hp : 0 ≤ frobeniusNorm M * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (M.toEuclideanLin x)]

end IdentityTesting.GeneralSignedMatrix
