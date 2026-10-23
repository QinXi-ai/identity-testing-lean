import IdentityTesting.GeneralSignedMatrixScalar
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact quadratic exponential integral for independent standard Gaussian coordinates. -/
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace IdentityTesting.GeneralSignedMatrix

theorem gaussian_quadratic_integral {c : ℝ} (hc : c < 1) :
    (∫ z : ℝ, Real.exp (c * z ^ 2 / 2) ∂gaussianReal 0 1) =
      1 / Real.sqrt (1 - c) := by
  have hs := gaussian_quadratic_integral_sq hc
  have hp : 0 < 1 - c := sub_pos.mpr hc
  have hr : (1 / Real.sqrt (1 - c)) ^ 2 = 1 / (1 - c) := by
    rw [div_pow, one_pow, Real.sq_sqrt hp.le]
  have hi : 0 ≤ ∫ z : ℝ, Real.exp (c * z ^ 2 / 2) ∂gaussianReal 0 1 :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hq : 0 ≤ 1 / Real.sqrt (1 - c) := by positivity
  nlinarith

theorem gaussian_diagonal_quadratic_integral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1) :
    (∫ z : ι → ℝ, Real.exp (∑ i, a i * z i ^ 2 / 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, 1 / Real.sqrt (1 - a i) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) => Real.exp (a i * x ^ 2 / 2))]
  exact Finset.prod_congr rfl (fun i _ => gaussian_quadratic_integral (ha i))

theorem gaussian_diagonal_quadratic_integral_det {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1) :
    (∫ z : ι → ℝ, Real.exp (∑ i, a i * z i ^ 2 / 2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      1 / Real.sqrt (∏ i, (1 - a i)) := by
  rw [gaussian_diagonal_quadratic_integral a ha, Finset.prod_div_distrib]
  simp only [Finset.prod_const_one]
  congr 1
  have hp : 0 ≤ ∏ i, Real.sqrt (1 - a i) :=
    Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hs : (∏ i, Real.sqrt (1 - a i)) ^ 2 = ∏ i, (1 - a i) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => Real.sq_sqrt (by linarith [ha i]))
  have hn : 0 ≤ ∏ i, (1 - a i) := Finset.prod_nonneg (fun i _ => by linarith [ha i])
  have hroot := Real.sq_sqrt hn
  have hroot0 := Real.sqrt_nonneg (∏ i, (1 - a i))
  nlinarith

end IdentityTesting.GeneralSignedMatrix
