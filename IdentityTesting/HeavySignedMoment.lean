import IdentityTesting.HeavySignedRankOne
import IdentityTesting.HeavySignedBudget

/-! # Exponential moment of the actual heavy signed likelihood structure -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavySignedMoment

open HeavySignedFamily HeavySignedBudget HeavySignedRankOne SignedDiagonalMoment

variable {k : ℕ}

def pairExp (f : (Fin k → Bool) → (Fin k → Bool) → ℝ) : ℝ :=
  ∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
    (uniformSigns k).mass σ * (uniformSigns k).mass τ * Real.exp (f σ τ)

theorem pairExp_nonneg (f : (Fin k → Bool) → (Fin k → Bool) → ℝ) : 0 ≤ pairExp f := by
  exact Finset.sum_nonneg (fun σ _ => Finset.sum_nonneg (fun τ _ =>
    mul_nonneg (mul_nonneg ((uniformSigns k).nonneg σ) ((uniformSigns k).nonneg τ)) (Real.exp_pos _).le))

theorem pairExp_cauchy
    (f g : (Fin k → Bool) → (Fin k → Bool) → ℝ) :
    (pairExp (fun σ τ => f σ τ + g σ τ)) ^ 2 ≤
      pairExp (fun σ τ => 2 * f σ τ) * pairExp (fun σ τ => 2 * g σ τ) := by
  let w (z : (Fin k → Bool) × (Fin k → Bool)) : ℝ :=
    (uniformSigns k).mass z.1 * (uniformSigns k).mass z.2
  have hw (z : (Fin k → Bool) × (Fin k → Bool)) : 0 ≤ w z :=
    mul_nonneg ((uniformSigns k).nonneg _) ((uniformSigns k).nonneg _)
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.univ : Finset ((Fin k → Bool) × (Fin k → Bool)))
    (r := fun z => w z * Real.exp (f z.1 z.2 + g z.1 z.2))
    (f := fun z => w z * Real.exp (2 * f z.1 z.2))
    (g := fun z => w z * Real.exp (2 * g z.1 z.2))
    (fun z _ => mul_nonneg (hw z) (Real.exp_pos _).le)
    (fun z _ => mul_nonneg (hw z) (Real.exp_pos _).le) ?_
  · simpa only [pairExp, w, Fintype.sum_prod_type] using h
  · intro z _
    calc
      _ = (w z) ^ 2 * Real.exp (2 * (f z.1 z.2 + g z.1 z.2)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
      _ = (w z) ^ 2 * (Real.exp (2 * f z.1 z.2) * Real.exp (2 * g z.1 z.2)) := by
        rw [← Real.exp_add]
        congr 1
        congr 1
        ring
      _ = _ := by ring

theorem reciprocal_le_exp_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    1 / (1 - y) ≤ Real.exp (2 * y) := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - y)).2
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * y))
    (by linarith : 0 ≤ 1 - y)
  have hprod := mul_nonneg hy0 (show 0 ≤ 1 - 2 * y by linarith)
  nlinarith only [h, hprod]

theorem pairExp_diagonal_le (d : Fin k → ℝ) (n : ℝ) :
    pairExp (fun σ τ => 2 * (n * diagonalInteraction d σ τ)) ≤
      Real.exp (2 * n ^ 2 * (∑ i, d i ^ 2)) := by
  have h := uniformSigns_pair_mgf_le (fun i => (2 * n) * d i)
  have heq : (∑ i, ((2 * n) * d i) ^ 2 / 2) = 2 * n ^ 2 * (∑ i, d i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [diagonalInteraction_smul] at h
  rw [heq] at h
  simpa only [pairExp, mul_assoc] using h

/-- Structured matrix bound: a diagonal plus the actual heavy head's rank-one
term. Both exponential moments are proved, rather than passed by the caller. -/
theorem structured_pairExp_le
    (d a : Fin k → ℝ) {h n D : ℝ} (hh : 0 < h)
    (hD : D = ∑ i, d i ^ 2)
    (hrank : (rankVariance a) ^ 2 / h ^ 2 ≤ D / 9)
    (hsmall : n ^ 2 * D ≤ 1 / 4) :
    pairExp (fun σ τ => n * (diagonalInteraction d σ τ +
      signedSum a σ * signedSum a τ / h)) ≤ Real.exp (2 * n ^ 2 * D) := by
  have hD0 : 0 ≤ D := by rw [hD]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  let y : ℝ := (2 * n / h) ^ 2 * (rankVariance a) ^ 2
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hybound : y ≤ (4 / 9 : ℝ) * (n ^ 2 * D) := by
    have h := mul_le_mul_of_nonneg_left hrank (show 0 ≤ 4 * n ^ 2 by positivity)
    convert h using 1 <;> dsimp [y] <;> ring
  have hyhalf : y ≤ 1 / 2 := by nlinarith only [hybound, hsmall]
  have hyrank : pairExp (fun σ τ => 2 * (n * (signedSum a σ * signedSum a τ / h))) ≤
      Real.exp (2 * y) := by
    have hrankMgf := uniformSigns_rankOne_mgf_le a (2 * n / h) (by
      change y < 1
      linarith only [hyhalf])
    have heq : pairExp (fun σ τ => 2 * (n * (signedSum a σ * signedSum a τ / h))) =
        (∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
          (uniformSigns k).mass σ * (uniformSigns k).mass τ *
            Real.exp ((2 * n / h) * signedSum a σ * signedSum a τ)) := by
      unfold pairExp
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      congr 1
      congr 1
      ring
    rw [heq]
    exact hrankMgf.trans (reciprocal_le_exp_two_mul hy0 hyhalf)
  have hcs := pairExp_cauchy (fun σ τ => n * diagonalInteraction d σ τ)
    (fun σ τ => n * (signedSum a σ * signedSum a τ / h))
  have hdiag := pairExp_diagonal_le d n
  rw [← hD] at hdiag
  have hcs' : (pairExp (fun σ τ => n * (diagonalInteraction d σ τ +
      signedSum a σ * signedSum a τ / h))) ^ 2 ≤
      Real.exp (2 * n ^ 2 * D) * Real.exp (2 * y) := by
    have h := hcs.trans (mul_le_mul hdiag hyrank (pairExp_nonneg _)
      (Real.exp_pos _).le)
    convert h using 1
    congr 1
    unfold pairExp
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    congr 1
    ring
  have hsq : (pairExp (fun σ τ => n * (diagonalInteraction d σ τ +
      signedSum a σ * signedSum a τ / h))) ^ 2 ≤
      (Real.exp (2 * n ^ 2 * D)) ^ 2 := by
    apply hcs'.trans
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnD : 0 ≤ n ^ 2 * D := mul_nonneg (sq_nonneg n) hD0
    norm_num
    nlinarith only [hybound, hnD]
  have hnonneg := pairExp_nonneg (fun σ τ => n * (diagonalInteraction d σ τ +
    signedSum a σ * signedSum a τ / h))
  have hpos := Real.exp_pos (2 * n ^ 2 * D)
  nlinarith only [hsq, hnonneg, hpos]

end IdentityTesting.HeavySignedMoment
