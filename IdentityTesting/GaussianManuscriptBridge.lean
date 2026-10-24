import IdentityTesting.GaussianGramIntegral
import IdentityTesting.GaussianRademacherBridge

/-! The Gaussian comparison at the actual symmetric signed-matrix input. -/
noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedMoment SignedDiagonalMoment

theorem gaussian_pi_norm_integral {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∫ z : Fin d → ℝ, Real.exp (t ^ 2 * (∑ i, (∑ j, M i j * z j) ^ 2) / 2)
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
      1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det := by
  have h := gaussian_norm_integral M t hsmall
  unfold standardGaussianVector at h
  rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))] at h
  simpa only [PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ), Real.norm_eq_abs, sq_abs,
    Matrix.toEuclideanLin_apply, PiLp.toLp_apply, Matrix.mulVec, dotProduct] using h

theorem gaussian_pi_norm_integrable {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    Integrable (fun z : Fin d → ℝ => Real.exp (t ^ 2 * (∑ i, (∑ j, M i j * z j) ^ 2) / 2))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  by_contra hn
  have hi := gaussian_pi_norm_integral M t hsmall
  rw [integral_undef hn] at hi
  have hA := (Matrix.posSemidef_conjTranspose_mul_self M).smul (sq_nonneg t)
  have ht : (t ^ 2 • (Mᴴ * M)).trace ≤ 1 / 2 := by
    rwa [gram_trace_eq_frobenius]
  have hp := (posSemidef_inverse_sqrt_det_le_exp_trace _ hA ht).1
  have hr : 0 < 1 / Real.sqrt (1 - t ^ 2 • (Mᴴ * M)).det := by positivity
  linarith

theorem symmetric_signed_gaussian_determinant_bound {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (t : ℝ)
    (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (t ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2)) ≤
        1 / Real.sqrt (1 - t ^ 2 • (M * M)).det ∧
    1 / Real.sqrt (1 - t ^ 2 • (M * M)).det ≤ Real.exp (t ^ 2 * frobeniusSq M) := by
  have hh : Mᴴ = M := hM
  have hsym (i j : Fin d) : M i j = M j i := by
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A j i) hh
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have he (z : Fin d → ℝ) : (∑ j, (∑ i, M i j * z i) ^ 2) =
      ∑ j, (∑ i, M j i * z i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym i j]
  refine ⟨?_, by simpa only [hh] using (gaussian_gram_integral M t hsmall).2⟩
  rw [gaussian_signed_matrix_swap]
  calc
    _ ≤ ∫ z : Fin d → ℝ, Real.exp (t ^ 2 * (∑ i, (∑ j, M i j * z j) ^ 2) / 2)
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
      apply integral_mono (gaussian_signed_matrix_sum_integrable M t)
        (gaussian_pi_norm_integrable M t hsmall)
      intro z
      simpa only [he z] using gaussian_signed_matrix_pointwise M t z
    _ = _ := by simpa only [hh] using gaussian_pi_norm_integral M t hsmall

theorem manuscript_signed_gaussian_comparison {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian) (n : ℕ)
    (hsmall : (n : ℝ) * frobeniusNorm M ≤ 1 / 2) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp ((n : ℝ) ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2)) ≤
        1 / Real.sqrt (1 - (n : ℝ) ^ 2 • (M * M)).det ∧
    (∫ x : EuclideanSpace ℝ (Fin d),
      Real.exp ((n : ℝ) ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2)
      ∂standardGaussianVector (Fin d)) =
        1 / Real.sqrt (1 - (n : ℝ) ^ 2 • (M * M)).det ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp ((n : ℝ) ^ 2 * ‖M.toEuclideanLin x‖ ^ 2 / 2))
        (standardGaussianVector (Fin d)) ∧
    1 / Real.sqrt (1 - (n : ℝ) ^ 2 • (M * M)).det ≤
      Real.exp ((n : ℝ) ^ 2 * frobeniusSq M) := by
  have hn : 0 ≤ (n : ℝ) * frobeniusNorm M :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hs : (n : ℝ) ^ 2 * frobeniusSq M ≤ 1 / 2 := by
    have hsq := pow_le_pow_left₀ hn hsmall 2
    rw [mul_pow, frobeniusNorm_sq] at hsq
    norm_num at hsq
    linarith
  exact ⟨(symmetric_signed_gaussian_determinant_bound M hM n hs).1,
    (gaussian_symmetric_norm_integral M hM n hsmall).1,
    gaussian_norm_integrable M n hs,
    (symmetric_signed_gaussian_determinant_bound M hM n hs).2⟩

end IdentityTesting.GeneralSignedMatrix
