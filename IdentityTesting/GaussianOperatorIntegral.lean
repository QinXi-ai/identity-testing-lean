import IdentityTesting.GaussianVectorInvariant
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! Gaussian quadratic integration in an orthonormal eigenbasis. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem quadratic_eq_eigenbasis_sum {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (a : ι → ℝ)
    (heig : ∀ i, T (b i) = a i • b i) (x : EuclideanSpace ℝ ι) :
    inner ℝ x (T x) = ∑ i, a i * (b.repr x i) ^ 2 := by
  have hcoord (i : ι) : b.repr (T x) i = a i * b.repr x i := by
    rw [b.repr_apply_apply, ← hT, heig, real_inner_smul_left, ← b.repr_apply_apply]
  rw [← b.repr.inner_map_map x (T x), PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change b.repr (T x) i * b.repr x i = _
  rw [hcoord]
  ring

theorem gaussian_operator_quadratic_integral {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (a : ι → ℝ)
    (heig : ∀ i, T (b i) = a i • b i) (ha : ∀ i, a i < 1) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (T x) / 2)
      ∂standardGaussianVector ι) = 1 / Real.sqrt (∏ i, (1 - a i)) := by
  have hc : Continuous T := T.continuous_of_finiteDimensional
  calc
    _ = ∫ z : EuclideanSpace ℝ ι, Real.exp ((∑ i, a i * (z i) ^ 2) / 2)
        ∂standardGaussianVector ι := by
      conv_lhs => rw [← standardGaussianVector_map_isometry b.repr.symm]
      rw [integral_map b.repr.symm.continuous.measurable.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [quadratic_eq_eigenbasis_sum T hT b a heig]
      simp only [LinearIsometryEquiv.apply_symm_apply]
    _ = _ := by
      unfold standardGaussianVector
      rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop))]
      simpa only [PiLp.toLp_apply, Finset.sum_div] using
        gaussian_diagonal_quadratic_integral_det a ha

theorem gaussian_operator_quadratic_integrable {ι : Type*} [Fintype ι]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι)) (a : ι → ℝ)
    (heig : ∀ i, T (b i) = a i • b i) (ha : ∀ i, a i < 1) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (inner ℝ x (T x) / 2))
      (standardGaussianVector ι) := by
  by_contra hn
  have hi := gaussian_operator_quadratic_integral T hT b a heig ha
  rw [integral_undef hn] at hi
  have hp : 0 < ∏ i, (1 - a i) := Finset.prod_pos (fun i _ => sub_pos.mpr (ha i))
  have hr : 0 < 1 / Real.sqrt (∏ i, (1 - a i)) := by positivity
  linarith

end IdentityTesting.GeneralSignedMatrix
