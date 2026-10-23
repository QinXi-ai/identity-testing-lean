import IdentityTesting.GeneralSignedMatrixScalar

/-! Product bound used for the eigenvalues in the Gaussian determinant estimate. -/
noncomputable section
namespace IdentityTesting.GeneralSignedMatrix
open scoped BigOperators
open HeavySignedMoment

theorem inverse_sqrt_product_le_exp_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ 1 / 2) :
    1 / Real.sqrt (∏ i, (1 - a i)) ≤ Real.exp (∑ i, a i) := by
  have hden : ∀ i, 0 < 1 - a i := fun i => by linarith [ha i]
  have hd : 0 < ∏ i, (1 - a i) := Finset.prod_pos (fun i _ => hden i)
  have hp := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) =>
      div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (hden i).le)
    (fun i (_ : i ∈ Finset.univ) => reciprocal_le_exp_two_mul (ha0 i) (ha i))
  have hprod : (∏ i, (1 / (1 - a i))) = 1 / ∏ i, (1 - a i) := by simp
  have hexp : (∏ i, Real.exp (2 * a i)) = (Real.exp (∑ i, a i)) ^ 2 := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    exact Real.exp_nat_mul _ 2
  rw [hprod, hexp] at hp
  have hs : (1 / Real.sqrt (∏ i, (1 - a i))) ^ 2 = 1 / ∏ i, (1 - a i) := by
    rw [div_pow, Real.sq_sqrt hd.le, one_pow]
  have he := Real.exp_pos (∑ i, a i)
  have hs0 : 0 ≤ 1 / Real.sqrt (∏ i, (1 - a i)) := by positivity
  nlinarith

end IdentityTesting.GeneralSignedMatrix
