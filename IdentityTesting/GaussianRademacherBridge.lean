import IdentityTesting.GaussianVectorMGF
import IdentityTesting.GeneralSignedMatrixMoment

/-! The actual finite-sign/Gaussian interchange in the signed-matrix proof. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedMoment SignedDiagonalMoment

theorem gaussian_finite_linear_average {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (w : Ω → ℝ) (a : Ω → ι → ℝ) :
    (∑ s, w s * Real.exp ((∑ i, a s i ^ 2) / 2)) =
      ∫ z : ι → ℝ, (∑ s, w s * Real.exp (∑ i, a s i * z i))
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  rw [integral_finset_sum _ (fun s _ =>
    (integrable_gaussian_vector_linear (a s)).const_mul (w s))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_const_mul, gaussian_vector_linear_integral]

theorem gaussian_signed_matrix_swap {d : ℕ} (M : Fin d → Fin d → ℝ) (t : ℝ) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (t ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2)) =
      ∫ z : Fin d → ℝ,
        (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
          Real.exp (t * ∑ i, z i * signedSum (M i) σ))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  have h := gaussian_finite_linear_average (uniformSigns d).mass
    (fun σ i => t * signedSum (M i) σ)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro σ _
    congr 2
    simp only [mul_pow, Finset.mul_sum]
  · apply integral_congr_ae
    filter_upwards [] with z
    apply Finset.sum_congr rfl
    intro σ _
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem gaussian_signed_matrix_pointwise {d : ℕ} (M : Fin d → Fin d → ℝ)
    (t : ℝ) (z : Fin d → ℝ) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (t * ∑ i, z i * signedSum (M i) σ)) ≤
        Real.exp (t ^ 2 * (∑ j, (∑ i, M i j * z i) ^ 2) / 2) := by
  have he (σ : Fin d → Bool) :
      (∑ i, z i * signedSum (M i) σ) = signedSum (fun j => ∑ i, M i j * z i) σ := by
    unfold signedSum
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  exact uniformSigns_linear_mgf_le _ t

theorem gaussian_signed_matrix_sum_integrable {d : ℕ} (M : Fin d → Fin d → ℝ) (t : ℝ) :
    Integrable (fun z : Fin d → ℝ => ∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (t * ∑ i, z i * signedSum (M i) σ))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  apply integrable_finset_sum
  intro σ _
  have h := (integrable_gaussian_vector_linear (fun i => t * signedSum (M i) σ)).const_mul
    ((uniformSigns d).mass σ)
  convert h using 1
  ext z
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end IdentityTesting.GeneralSignedMatrix
