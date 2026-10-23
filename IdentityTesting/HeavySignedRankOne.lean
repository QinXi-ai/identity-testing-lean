import IdentityTesting.HeavySignedFamily
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# A one-dimensional bound for the heavy prior's rank-one term

Only a real Gaussian exponential moment is used. There is no multivariate
Gaussian, spectral decomposition, determinant formula, or assumed MGF bound.
-/

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

namespace IdentityTesting.HeavySignedRankOne

open HeavySignedFamily SignedDiagonalMoment

theorem gaussian_quadratic_density (c z : ℝ) :
    gaussianPDFReal 0 1 z * Real.exp (c * z ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - c) / 2) * z ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

theorem integrable_gaussian_quadratic {c : ℝ} (hc : c < 1) :
    Integrable (fun z : ℝ => Real.exp (c * z ^ 2 / 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun z => gaussianPDF_lt_top (μ := 0) (v := 1) (x := z)))).2
  have h := (integrable_exp_neg_mul_sq (by linarith : 0 < (1 - c) / 2)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert h using 1
  funext z
  simp only [toReal_gaussianPDF]
  rw [mul_comm]
  exact gaussian_quadratic_density c z

theorem gaussian_quadratic_integral_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    (∫ z : ℝ, Real.exp (c * z ^ 2 / 2) ∂gaussianReal 0 1) ≤ 1 / (1 - c) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_quadratic_density]
  rw [integral_const_mul, integral_gaussian]
  have hd : 0 < 1 - c := sub_pos.mpr hc1
  let I : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / ((1 - c) / 2))
  have hI2 : I ^ 2 = 1 / (1 - c) := by
    dsimp [I]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp [Real.pi_ne_zero, ne_of_gt hd]
  change I ≤ 1 / (1 - c)
  apply (le_div_iff₀ hd).2
  have hsq : (I * (1 - c)) ^ 2 ≤ 1 := by
    calc
      _ = 1 - c := by rw [mul_pow, hI2]; field_simp
      _ ≤ 1 := by linarith only [hc0]
  nlinarith only [hsq, sq_nonneg (I * (1 - c) - 1)]

theorem gaussian_linear_integral (t : ℝ) :
    (∫ z : ℝ, Real.exp (t * z) ∂gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  simpa only [mgf, id_eq, NNReal.coe_one, zero_mul, zero_add, one_mul] using
    congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t

theorem uniformSigns_square_mgf_le {k : ℕ} (a : Fin k → ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c * (∑ i, a i ^ 2) < 1) :
    (∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
      Real.exp (c * (signedSum a σ) ^ 2 / 2)) ≤
        1 / (1 - c * (∑ i, a i ^ 2)) := by
  let μ := gaussianReal 0 1
  have hi : ∀ σ : Fin k → Bool, Integrable
      (fun z : ℝ => (uniformSigns k).mass σ * Real.exp ((Real.sqrt c * signedSum a σ) * z)) μ := by
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
  have hright := integrable_gaussian_quadratic hc1
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
    _ ≤ _ := gaussian_quadratic_integral_le
      (mul_nonneg hc0 (Finset.sum_nonneg (fun i _ => sq_nonneg _))) hc1

theorem uniformSigns_rankOne_mgf_le {k : ℕ} (a : Fin k → ℝ) (t : ℝ)
    (ht : t ^ 2 * (∑ i, a i ^ 2) ^ 2 < 1) :
    (∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
      (uniformSigns k).mass σ * (uniformSigns k).mass τ *
        Real.exp (t * signedSum a σ * signedSum a τ)) ≤
          1 / (1 - t ^ 2 * (∑ i, a i ^ 2) ^ 2) := by
  calc
    _ ≤ ∑ σ : Fin k → Bool, (uniformSigns k).mass σ *
        Real.exp ((t ^ 2 * (∑ i, a i ^ 2)) * (signedSum a σ) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ ((uniformSigns k).nonneg σ)
      have h := uniformSigns_linear_mgf_le a (t * signedSum a σ)
      convert h using 1
      · apply Finset.sum_congr rfl
        intro τ _
        congr 1
        congr 1
        ring
      · congr 1
        ring
    _ ≤ _ := by
      have h := uniformSigns_square_mgf_le a
        (mul_nonneg (sq_nonneg t) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
        (show (t ^ 2 * (∑ i, a i ^ 2)) * (∑ i, a i ^ 2) < 1 by nlinarith only [ht])
      convert h using 1; ring

end IdentityTesting.HeavySignedRankOne
