import IdentityTesting.GaussianOperatorIntegral
import IdentityTesting.GaussianDeterminantBound

/-! Exact Gaussian matrix integral and its trace bound. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem gaussian_matrix_quadratic_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (ha : ∀ i, hA.eigenvalues i < 1) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (A.toEuclideanLin x) / 2)
      ∂standardGaussianVector ι) = 1 / Real.sqrt (1 - A).det := by
  rw [hermitian_det_one_sub A hA]
  apply gaussian_operator_quadratic_integral A.toEuclideanLin
    (Matrix.isHermitian_iff_isSymmetric.mp hA) hA.eigenvectorBasis hA.eigenvalues
    ?_ ha
  intro i
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

theorem gaussian_matrix_quadratic_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (ha : ∀ i, hA.eigenvalues i < 1) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (inner ℝ x (A.toEuclideanLin x) / 2))
      (standardGaussianVector ι) := by
  by_contra hn
  have hi := gaussian_matrix_quadratic_integral A hA ha
  rw [integral_undef hn, hermitian_det_one_sub A hA] at hi
  have hp : 0 < ∏ i, (1 - hA.eigenvalues i) :=
    Finset.prod_pos (fun i _ => sub_pos.mpr (ha i))
  have hr : 0 < 1 / Real.sqrt (∏ i, (1 - hA.eigenvalues i)) := by positivity
  linarith

theorem gaussian_posSemidef_integral_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (htr : A.trace ≤ 1 / 2) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (A.toEuclideanLin x) / 2)
      ∂standardGaussianVector ι) = 1 / Real.sqrt (1 - A).det ∧
    (∫ x : EuclideanSpace ℝ ι, Real.exp (inner ℝ x (A.toEuclideanLin x) / 2)
      ∂standardGaussianVector ι) ≤ Real.exp A.trace := by
  have he : ∀ i, hA.isHermitian.eigenvalues i < 1 := by
    intro i
    have ht : A.trace = ∑ j, hA.isHermitian.eigenvalues j :=
      hA.isHermitian.trace_eq_sum_eigenvalues
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    rw [← ht] at hi
    linarith
  have hi := gaussian_matrix_quadratic_integral A hA.isHermitian he
  exact ⟨hi, hi.le.trans (posSemidef_inverse_sqrt_det_le_exp_trace A hA htr).2⟩

end IdentityTesting.GeneralSignedMatrix
