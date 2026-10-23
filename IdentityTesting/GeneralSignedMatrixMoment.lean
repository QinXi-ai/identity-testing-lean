import IdentityTesting.GeneralSignedMatrixScalar
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! General bilinear Rademacher moment bound, using weighted Jensen over rows.
No symmetry, spectral theorem, determinant, or multivariate Gaussian is needed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedMoment SignedDiagonalMoment

def rowSquareSum {d : ℕ} (M : Fin d → Fin d → ℝ) (i : Fin d) : ℝ := ∑ j, M i j ^ 2
def frobeniusSq {d : ℕ} (M : Fin d → Fin d → ℝ) : ℝ := ∑ i, rowSquareSum M i
def frobeniusNorm {d : ℕ} (M : Fin d → Fin d → ℝ) : ℝ := Real.sqrt (frobeniusSq M)

theorem rowSquareSum_nonneg {d : ℕ} (M : Fin d → Fin d → ℝ) (i : Fin d) :
    0 ≤ rowSquareSum M i := Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem frobeniusSq_nonneg {d : ℕ} (M : Fin d → Fin d → ℝ) : 0 ≤ frobeniusSq M :=
  Finset.sum_nonneg (fun i _ => rowSquareSum_nonneg M i)

theorem rowSquareSum_le_frobeniusSq {d : ℕ} (M : Fin d → Fin d → ℝ) (i : Fin d) :
    rowSquareSum M i ≤ frobeniusSq M :=
  Finset.single_le_sum (fun j _ => rowSquareSum_nonneg M j) (Finset.mem_univ i)

theorem row_eq_zero_of_squareSum_zero {d : ℕ} {M : Fin d → Fin d → ℝ} {i : Fin d}
    (hi : rowSquareSum M i = 0) : ∀ j, M i j = 0 := by
  intro j
  have h : M i j ^ 2 ≤ rowSquareSum M i :=
    Finset.single_le_sum (fun l _ => sq_nonneg (M i l)) (Finset.mem_univ j)
  rw [hi] at h
  nlinarith

theorem signedSum_zero_of_rowSquareSum_zero {d : ℕ} {M : Fin d → Fin d → ℝ} {i : Fin d}
    (hi : rowSquareSum M i = 0) (σ : Fin d → Bool) : signedSum (M i) σ = 0 := by
  simp [signedSum, row_eq_zero_of_squareSum_zero hi]

theorem frobeniusNorm_sq {d : ℕ} (M : Fin d → Fin d → ℝ) :
    frobeniusNorm M ^ 2 = frobeniusSq M := Real.sq_sqrt (frobeniusSq_nonneg M)

/-- The normalized row-square Jensen argument. Zero rows and the zero matrix
are handled inside the theorem; no row-norm nonvanishing premise is required. -/
theorem uniformSigns_matrix_square_mgf_le {d : ℕ} (M : Fin d → Fin d → ℝ)
    (t : ℝ) (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
      Real.exp (t ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2)) ≤
        Real.exp (t ^ 2 * frobeniusSq M) := by
  by_cases hF0 : frobeniusSq M = 0
  · have hr0 : ∀ i, rowSquareSum M i = 0 := fun i =>
      le_antisymm (by simpa [hF0] using rowSquareSum_le_frobeniusSq M i) (rowSquareSum_nonneg M i)
    simp only [signedSum_zero_of_rowSquareSum_zero (hr0 _), zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, zero_div, Real.exp_zero, mul_one, hF0]
    exact le_of_eq (uniformSigns d).total
  · have hF : 0 < frobeniusSq M := lt_of_le_of_ne (frobeniusSq_nonneg M) (Ne.symm hF0)
    let w : Fin d → ℝ := fun i => rowSquareSum M i / frobeniusSq M
    let c : Fin d → ℝ := fun i => t ^ 2 * frobeniusSq M / rowSquareSum M i
    have hw0 : ∀ i, 0 ≤ w i := fun i => div_nonneg (rowSquareSum_nonneg M i) hF.le
    have hw1 : (∑ i, w i) = 1 := by
      dsimp [w]
      rw [← Finset.sum_div]
      exact div_self hF0
    have hc0 : ∀ i, 0 ≤ c i := fun i =>
      div_nonneg (mul_nonneg (sq_nonneg t) hF.le) (rowSquareSum_nonneg M i)
    have hcprod : ∀ i, c i * rowSquareSum M i ≤ t ^ 2 * frobeniusSq M := by
      intro i
      by_cases hi : rowSquareSum M i = 0
      · simp only [c, hi, div_zero, zero_mul]
        exact mul_nonneg (sq_nonneg t) hF.le
      · exact le_of_eq (div_mul_cancel₀ _ hi)
    have hrow : ∀ i, (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
        Real.exp (c i * signedSum (M i) σ ^ 2 / 2)) ≤ Real.exp (t ^ 2 * frobeniusSq M) := by
      intro i
      exact (uniformSigns_square_mgf_le_exp (M i) (hc0 i)
        ((hcprod i).trans hsmall)).trans (Real.exp_le_exp.mpr (hcprod i))
    have hpoint (σ : Fin d → Bool) :
        Real.exp (t ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2) ≤
          ∑ i, w i * Real.exp (c i * signedSum (M i) σ ^ 2 / 2) := by
      have harg : (∑ i, w i * (c i * signedSum (M i) σ ^ 2 / 2)) =
          t ^ 2 * (∑ i, signedSum (M i) σ ^ 2) / 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : rowSquareSum M i = 0
        · rw [signedSum_zero_of_rowSquareSum_zero hi]
          ring
        · dsimp [w, c]
          field_simp
      have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := w)
        (p := fun i => c i * signedSum (M i) σ ^ 2 / 2)
        (fun i _ => hw0 i) hw1 (fun i _ => Set.mem_univ _)
      simpa only [smul_eq_mul, harg] using h
    calc
      _ ≤ ∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
          (∑ i, w i * Real.exp (c i * signedSum (M i) σ ^ 2 / 2)) := by
        exact Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hpoint σ)
          ((uniformSigns d).nonneg σ))
      _ = ∑ i, w i * (∑ σ : Fin d → Bool, (uniformSigns d).mass σ *
          Real.exp (c i * signedSum (M i) σ ^ 2 / 2)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _ ≤ ∑ i, w i * Real.exp (t ^ 2 * frobeniusSq M) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw0 i))
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

theorem matrixInteraction_as_signedSum {d : ℕ} (M : Fin d → Fin d → ℝ)
    (σ τ : Fin d → Bool) :
    matrixInteraction M σ τ = signedSum (fun i => signedSum (M i) τ) σ := by
  unfold matrixInteraction signedSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- General real-matrix bilinear MGF with the manuscript exponent.
The result is stronger than the stated symmetric-matrix special case. -/
theorem matrix_pair_mgf_le_exp {d : ℕ} (M : Fin d → Fin d → ℝ)
    (t : ℝ) (hsmall : t ^ 2 * frobeniusSq M ≤ 1 / 2) :
    pairExp (fun σ τ => t * matrixInteraction M σ τ) ≤ Real.exp (t ^ 2 * frobeniusSq M) := by
  unfold pairExp
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ τ : Fin d → Bool, (uniformSigns d).mass τ *
        Real.exp (t ^ 2 * (∑ i, signedSum (M i) τ ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro τ _
      have h := uniformSigns_linear_mgf_le (fun i => signedSum (M i) τ) t
      have h' := mul_le_mul_of_nonneg_left h ((uniformSigns d).nonneg τ)
      simpa only [Finset.mul_sum, ← matrixInteraction_as_signedSum, mul_assoc, mul_left_comm] using h'
    _ ≤ _ := uniformSigns_matrix_square_mgf_le M t hsmall

end IdentityTesting.GeneralSignedMatrix
