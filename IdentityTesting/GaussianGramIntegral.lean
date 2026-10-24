import IdentityTesting.GaussianDeterminantIntegral
import IdentityTesting.GaussianMatrixGeometry
import Mathlib.Data.Real.StarOrdered

/-! The Gaussian determinant identity at the actual signed-matrix input. -/
noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem gaussian_gram_integral {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp (inner ℝ x ((t ^ 2 • (Mᴴ * M)).toEuclideanLin x) / 2)
      ∂standardGaussianVector (Fin d)) =
        1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det ∧
    1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det ≤
      Real.exp (t ^ 2 * frobeniusSq M) := by
  have hA := (Matrix.posSemidef_conjTranspose_mul_self M).smul (sq_nonneg t)
  have ht : (t ^ 2 • (Mᴴ * M)).trace ≤ 1 / 2 := by
    rwa [gram_trace_eq_frobenius]
  exact ⟨(gaussian_posSemidef_integral_bound _ hA ht).1,
    by simpa only [gram_trace_eq_frobenius] using
      (posSemidef_inverse_sqrt_det_le_exp_trace _ hA ht).2⟩

theorem gaussian_norm_integral {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (t ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2)
      ∂standardGaussianVector (Fin d)) =
        1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det := by
  simpa only [gram_quadratic_eq_norm_sq] using (gaussian_gram_integral M t hsmall).1

theorem gaussian_norm_integrable {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (t ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2)) (standardGaussianVector (Fin d)) := by
  by_contra hn
  have hi := gaussian_norm_integral M t hsmall
  rw [integral_undef hn] at hi
  have hA := (Matrix.posSemidef_conjTranspose_mul_self M).smul (sq_nonneg t)
  have ht : (t ^ 2 • (Mᴴ * M)).trace ≤ 1 / 2 := by
    rwa [gram_trace_eq_frobenius]
  have hp := (posSemidef_inverse_sqrt_det_le_exp_trace _ hA ht).1
  have hr : 0 < 1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det := by positivity
  linarith

theorem gaussian_symmetric_norm_integral {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.IsHermitian) (n : ℕ) (hsmall : (n : ℝ) * frobeniusNorm M ≤ 1 / 2) :
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp ((n : ℝ) ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2)
      ∂standardGaussianVector (Fin d)) =
        1 / Real.sqrt (1 - (n : ℝ) ^ 2 • (M * M)).det ∧
    1 / Real.sqrt (1 - (n : ℝ) ^ 2 • (M * M)).det ≤
      Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) := by
  have hn : 0 ≤ (n : ℝ) * frobeniusNorm M :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hs : (n : ℝ) ^ 2 * frobeniusSq M ≤ 1 / 2 := by
    have hsq : ((n : ℝ) * frobeniusNorm M) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hn hsmall 2
    rw [mul_pow, frobeniusNorm_sq] at hsq
    linarith
  have hh : Mᴴ = M := hM
  exact ⟨by simpa only [hh] using gaussian_norm_integral M n hs,
    by simpa only [hh] using (gaussian_gram_integral M n hs).2⟩

end IdentityTesting.GeneralSignedMatrix
