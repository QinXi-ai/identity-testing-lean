import IdentityTesting.GaussianDiagonalIntegral

/-! Linear exponential moments and integrability for independent Gaussian coordinates. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedMoment HeavySignedRankOne

theorem integrable_gaussian_vector_linear {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, a i * z i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a i))

theorem gaussian_vector_linear_integral {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∫ z : ι → ℝ, Real.exp (∑ i, a i * z i)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      Real.exp ((∑ i, a i ^ 2) / 2) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (a i * x))]
  simp_rw [gaussian_linear_integral]
  rw [← Real.exp_sum, ← Finset.sum_div]

theorem integrable_gaussian_vector_quadratic {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1) :
    Integrable (fun z : ι → ℝ => Real.exp (∑ i, a i * z i ^ 2 / 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_gaussian_quadratic (ha i))

end IdentityTesting.GeneralSignedMatrix
