import IdentityTesting.HeavySignedMoment

/-! Sharp scalar square-MGF bound for the general signed-matrix argument.
Only the already installed one-dimensional Gaussian integral is used. -/

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedRankOne HeavySignedMoment SignedDiagonalMoment

theorem gaussian_quadratic_integral_sq {c : ℝ} (hc : c < 1) :
    (∫ z : ℝ, Real.exp (c * z ^ 2 / 2) ∂gaussianReal 0 1) ^ 2 = 1 / (1 - c) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_quadratic_density]
  rw [integral_const_mul, integral_gaussian]
  have hd : 0 < 1 - c := sub_pos.mpr hc
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp [Real.pi_ne_zero, ne_of_gt hd]

theorem gaussian_quadratic_integral_le_exp {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    (∫ z : ℝ, Real.exp (c * z ^ 2 / 2) ∂gaussianReal 0 1) ≤ Real.exp c := by
  have hsq := gaussian_quadratic_integral_sq (show c < 1 by linarith)
  have hb := reciprocal_le_exp_two_mul hc0 hc1
  have he : Real.exp (2 * c) = (Real.exp c) ^ 2 := by
    simpa using Real.exp_nat_mul c 2
  rw [he] at hb
  nlinarith [Real.exp_pos c]

/-- Scalar subGaussian-square bound with the exponent needed by the original
signed-matrix TV estimate. The square MGF is derived from actual uniform signs. -/
theorem uniformSigns_square_mgf_le_exp {k : ℕ} (a : Fin k → ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c * (∑ i, a i ^ 2) ≤ 1 / 2) :
    (∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
      Real.exp (c * (signedSum a σ) ^ 2 / 2)) ≤
        Real.exp (c * (∑ i, a i ^ 2)) := by
  let μ := gaussianReal 0 1
  have hi : ∀ σ : Fin k → Bool, Integrable
      (fun z : ℝ => (uniformSigns k).mass σ *
        Real.exp ((Real.sqrt c * signedSum a σ) * z)) μ := by
    intro σ
    exact (integrable_exp_mul_gaussianReal _).const_mul _
  have hmgf (σ : Fin k → Bool) :
      (∫ z : ℝ, Real.exp ((Real.sqrt c * signedSum a σ) * z) ∂μ) =
        Real.exp (c * (signedSum a σ) ^ 2 / 2) := by
    rw [gaussian_linear_integral, mul_pow, Real.sq_sqrt hc0]
  have hpoint (z : ℝ) :
      (∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
        Real.exp ((Real.sqrt c * signedSum a σ) * z)) ≤
          Real.exp ((c * (∑ i, a i ^ 2)) * z ^ 2 / 2) := by
    calc
      _ = ∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
          Real.exp ((Real.sqrt c * z) * signedSum a σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        congr 1
        ring
      _ ≤ Real.exp ((Real.sqrt c * z) ^ 2 * (∑ i, a i ^ 2) / 2) :=
        uniformSigns_linear_mgf_le a (Real.sqrt c * z)
      _ = _ := by rw [mul_pow, Real.sq_sqrt hc0]; congr 1; ring
  have hright := integrable_gaussian_quadratic (show c * (∑ i, a i ^ 2) < 1 by linarith)
  calc
    _ = ∑ σ : Fin k → Bool, ∫ z : ℝ, (uniformSigns k).mass σ *
        Real.exp ((Real.sqrt c * signedSum a σ) * z) ∂μ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [integral_const_mul, hmgf]
    _ = ∫ z : ℝ, (∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
        Real.exp ((Real.sqrt c * signedSum a σ) * z)) ∂μ :=
      (integral_finset_sum _ (fun σ _ => hi σ)).symm
    _ ≤ ∫ z : ℝ, Real.exp ((c * (∑ i, a i ^ 2)) * z ^ 2 / 2) ∂μ :=
      integral_mono (integrable_finset_sum _ (fun σ _ => hi σ)) hright hpoint
    _ ≤ _ := gaussian_quadratic_integral_le_exp
      (mul_nonneg hc0 (Finset.sum_nonneg (fun i _ => sq_nonneg _))) hc1

end IdentityTesting.GeneralSignedMatrix
