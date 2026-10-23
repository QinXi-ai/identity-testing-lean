import IdentityTesting.GaussianDiagonalIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-! The standard Gaussian vector and its invariance under orthogonal changes of basis. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

def standardGaussianVector (ι : Type*) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (WithLp.toLp 2)

instance {ι : Type*} [Fintype ι] : IsProbabilityMeasure (standardGaussianVector ι) := by
  unfold standardGaussianVector
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_standardGaussianVector {ι : Type*} [Fintype ι]
    (t : EuclideanSpace ℝ ι) :
    charFun (standardGaussianVector ι) t = Complex.exp (-(‖t‖ : ℂ) ^ 2 / 2) := by
  rw [standardGaussianVector, charFun_pi]
  simp_rw [charFun_gaussianReal]
  simp only [NNReal.coe_one, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.ofReal_one, one_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]
  congr 2
  have ht : ‖t‖ ^ 2 = ∑ i, (t i) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) t
  exact_mod_cast ht.symm

theorem standardGaussianVector_map_isometry {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (standardGaussianVector ι).map U = standardGaussianVector ι := by
  apply Measure.ext_of_charFun
  funext t
  have hm : charFun ((standardGaussianVector ι).map U) t =
      charFun (standardGaussianVector ι) (U.symm t) := by
    rw [charFun_apply, integral_map U.continuous.measurable.aemeasurable (by fun_prop)]
    simp only [LinearIsometryEquiv.inner_map_eq_flip, charFun_apply]
  rw [hm, charFun_standardGaussianVector, charFun_standardGaussianVector, U.symm.norm_map]

end IdentityTesting.GeneralSignedMatrix
