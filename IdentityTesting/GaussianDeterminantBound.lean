import IdentityTesting.GaussianProductBound
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The determinant estimate in the manuscript's spectral Gaussian argument. -/
noncomputable section
namespace IdentityTesting.GeneralSignedMatrix
open scoped BigOperators
open HeavySignedMoment

theorem hermitian_det_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
    (1 - A).det = ∏ i, (1 - hA.eigenvalues i) := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hu : star U * U = 1 := unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hdiag : star U * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.star_mul_self_mul_eq_diagonal
  have hconj : star U * (1 - A) * U = Matrix.diagonal (fun i => 1 - hA.eigenvalues i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hu, hdiag]
    simpa only [Matrix.diagonal_one] using
      Matrix.diagonal_sub (fun _ : ι => (1 : ℝ)) hA.eigenvalues
  have hd := congrArg Matrix.det hconj
  have hud := congrArg Matrix.det hu
  simp only [Matrix.det_mul, Matrix.det_one] at hud
  simp only [Matrix.det_mul, Matrix.det_diagonal] at hd
  calc
    (1 - A).det = (star U).det * (1 - A).det * U.det := by rw [mul_right_comm, hud, one_mul]
    _ = _ := hd

theorem posSemidef_inverse_sqrt_det_le_exp_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (htr : A.trace ≤ 1 / 2) :
    0 < (1 - A).det ∧ 1 / Real.sqrt (1 - A).det ≤ Real.exp A.trace := by
  have ht : A.trace = ∑ i, hA.isHermitian.eigenvalues i := hA.isHermitian.trace_eq_sum_eigenvalues
  have he0 : ∀ i, 0 ≤ hA.isHermitian.eigenvalues i := hA.eigenvalues_nonneg
  have he : ∀ i, hA.isHermitian.eigenvalues i ≤ 1 / 2 := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => he0 j) (Finset.mem_univ i)
    rw [← ht] at h
    exact h.trans htr
  rw [hermitian_det_one_sub A hA.isHermitian, ht]
  exact ⟨Finset.prod_pos (fun i _ => by linarith [he i]),
    inverse_sqrt_product_le_exp_sum _ he0 he⟩

end IdentityTesting.GeneralSignedMatrix
