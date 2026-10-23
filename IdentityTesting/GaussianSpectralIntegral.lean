import IdentityTesting.GaussianOperatorIntegral
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Gaussian integration using the eigenbasis constructed by the spectral theorem. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem selfadjoint_eigenvalues_lt_one {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : T.toLinearMap.IsSymmetric) (hsmall : ‖T‖ < 1) :
    ∀ i : Fin d, hT.eigenvalues (n := d) (by simp) i < 1 := by
  let hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  intro i
  have he : T (hT.eigenvectorBasis hd i) =
      hT.eigenvalues hd i • hT.eigenvectorBasis hd i := by
    exact hT.apply_eigenvectorBasis hd i
  have hu := (hT.eigenvectorBasis hd).orthonormal.1 i
  have hb := T.le_opNorm (hT.eigenvectorBasis hd i)
  rw [he, norm_smul, Real.norm_eq_abs, hu, mul_one, mul_one] at hb
  exact ((le_abs_self _).trans hb).trans_lt hsmall

theorem gaussian_selfadjoint_integral {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : T.toLinearMap.IsSymmetric) (hsmall : ‖T‖ < 1) :
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (inner ℝ x (T x) / 2)
      ∂standardGaussianVector (Fin d)) =
      1 / Real.sqrt (∏ i : Fin d, (1 - hT.eigenvalues (n := d) (by simp) i)) := by
  apply gaussian_operator_quadratic_integral T.toLinearMap hT
    (hT.eigenvectorBasis (n := d) (by simp)) (hT.eigenvalues (n := d) (by simp))
  · intro i
    exact hT.apply_eigenvectorBasis (n := d) (by simp) i
  · exact selfadjoint_eigenvalues_lt_one T hT hsmall

theorem gaussian_selfadjoint_integrable {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hT : T.toLinearMap.IsSymmetric) (hsmall : ‖T‖ < 1) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (inner ℝ x (T x) / 2))
      (standardGaussianVector (Fin d)) := by
  apply gaussian_operator_quadratic_integrable T.toLinearMap hT
    (hT.eigenvectorBasis (n := d) (by simp)) (hT.eigenvalues (n := d) (by simp))
  · intro i
    exact hT.apply_eigenvectorBasis (n := d) (by simp) i
  · exact selfadjoint_eigenvalues_lt_one T hT hsmall

end IdentityTesting.GeneralSignedMatrix
