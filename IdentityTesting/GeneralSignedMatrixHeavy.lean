import IdentityTesting.GeneralSignedMatrixTV
import IdentityTesting.HeavySignedBudget

/-! The actual heavy signed likelihood matrix, its manuscript Frobenius bound,
and the exact signed-mixture error. Existing heavy laws and budget constructions
are reused without introducing a replacement lower-bound construction. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.GeneralSignedMatrix
open HeavySignedFamily HeavySignedBudget SignedDiagonalMoment FiniteTesting

variable {k : ℕ}

theorem frobeniusSq_likelihoodMatrix (q : Probability (Fin (k + 1))) (a : Fin k → ℝ) :
    frobeniusSq (likelihoodMatrix q a) = diagonalEnergy q a +
      2 * (∑ i, (a i ^ 2 / q.mass i.succ) * a i ^ 2) / q.mass 0 +
      rankVariance a ^ 2 / q.mass 0 ^ 2 := by
  classical
  have hd : (∑ i : Fin k, ∑ j : Fin k,
      (if i = j then a i ^ 2 / q.mass i.succ else 0) ^ 2) = diagonalEnergy q a := by
    simp [diagonalEnergy, ite_pow]
  have hc : (∑ i : Fin k, ∑ j : Fin k,
      2 * (if i = j then a i ^ 2 / q.mass i.succ else 0) *
        (a i * a j / q.mass 0)) =
      2 * (∑ i, (a i ^ 2 / q.mass i.succ) * a i ^ 2) / q.mass 0 := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring
  have hr : (∑ i : Fin k, ∑ j : Fin k, (a i * a j / q.mass 0) ^ 2) =
      rankVariance a ^ 2 / q.mass 0 ^ 2 := by
    simp only [div_pow, mul_pow, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul,
      rankVariance]
    ring
  unfold frobeniusSq rowSquareSum likelihoodMatrix
  simp only [add_sq, Finset.sum_add_distrib]
  rw [hd, hc, hr]

theorem diagonal_entry_le_sqrt_energy (q : Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (i : Fin k) : a i ^ 2 / q.mass i.succ ≤ Real.sqrt (diagonalEnergy q a) := by
  have hi : (a i ^ 2 / q.mass i.succ) ^ 2 ≤ diagonalEnergy q a :=
    Finset.single_le_sum (fun j _ => sq_nonneg (a j ^ 2 / q.mass j.succ)) (Finset.mem_univ i)
  have hs := Real.sq_sqrt (diagonalEnergy_nonneg q a)
  have hs0 := Real.sqrt_nonneg (diagonalEnergy q a)
  nlinarith

/-- The first inequality of `hh:signed-norm`, for the actual likelihood matrix. -/
theorem likelihoodMatrix_frobenius_triangle (q : Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) :
    frobeniusNorm (likelihoodMatrix q a) ≤
      Real.sqrt (diagonalEnergy q a) + rankVariance a / q.mass 0 := by
  have hc : (∑ i, (a i ^ 2 / q.mass i.succ) * a i ^ 2) ≤
      Real.sqrt (diagonalEnergy q a) * rankVariance a := by
    unfold rankVariance
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (diagonal_entry_le_sqrt_energy q a i) (sq_nonneg _))
  have hcd := div_le_div_of_nonneg_right hc (hq 0).le
  have hf := frobeniusNorm_sq (likelihoodMatrix q a)
  rw [frobeniusSq_likelihoodMatrix] at hf
  have hs := Real.sq_sqrt (diagonalEnergy_nonneg q a)
  have hs0 := Real.sqrt_nonneg (diagonalEnergy q a)
  have hv0 := div_nonneg (rankVariance_nonneg a) (hq 0).le
  have hv : (rankVariance a / q.mass 0) ^ 2 = rankVariance a ^ 2 / q.mass 0 ^ 2 := div_pow _ _ _
  rw [← hv] at hf
  simp only [mul_div_assoc] at hf hcd
  have hfv : frobeniusNorm (likelihoodMatrix q a) ^ 2 ≤
      (Real.sqrt (diagonalEnergy q a) + rankVariance a / q.mass 0) ^ 2 := by
    nlinarith [hcd]
  nlinarith

/-- The second inequality of `hh:signed-norm`, before using R ≤ 1/4. -/
theorem likelihoodMatrix_frobenius_head_tail (q : Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) :
    frobeniusNorm (likelihoodMatrix q a) ≤
      (1 + tailTotal q / q.mass 0) * Real.sqrt (diagonalEnergy q a) := by
  have hR0 : 0 ≤ tailTotal q := Finset.sum_nonneg (fun i _ => q.nonneg i.succ)
  have hv0 := rankVariance_nonneg a
  have hcs := rankVariance_sq_le q a hq
  have hs := Real.sq_sqrt (diagonalEnergy_nonneg q a)
  have hs0 := Real.sqrt_nonneg (diagonalEnergy q a)
  have hv : rankVariance a ≤ tailTotal q * Real.sqrt (diagonalEnergy q a) := by
    have he : (tailTotal q * Real.sqrt (diagonalEnergy q a)) ^ 2 =
        diagonalEnergy q a * tailTotal q ^ 2 := by rw [mul_pow, hs]; ring
    nlinarith [mul_nonneg hR0 hs0]
  have hvd := div_le_div_of_nonneg_right hv (hq 0).le
  have ht := likelihoodMatrix_frobenius_triangle q a hq
  calc
    _ ≤ Real.sqrt (diagonalEnergy q a) +
        (tailTotal q * Real.sqrt (diagonalEnergy q a)) / q.mass 0 := add_le_add_left hvd _ |>.trans' ht
    _ = _ := by ring

/-- Original `hh:signed-norm`: the actual allocation amplitudes give 64/(3T). -/
theorem allocation_likelihoodMatrix_frobenius_bound
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR : tailTotal q ≤ (1 : ℝ) / 4) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) = 1) :
    frobeniusNorm (likelihoodMatrix q (allocationAmplitude q x)) ≤ 64 / (3 * T) := by
  have htotal := reference_head_tail q
  have hratio : tailTotal q / q.mass 0 ≤ 1 / 3 := by
    apply (div_le_iff₀ (hq 0)).2
    linarith
  have hd := allocation_diagonalEnergy_bound q x hq hx hT hbudget
  have hs := Real.sq_sqrt (diagonalEnergy_nonneg q (allocationAmplitude q x))
  have hs0 := Real.sqrt_nonneg (diagonalEnergy q (allocationAmplitude q x))
  have hu0 : 0 ≤ 16 / T := div_nonneg (by norm_num) hT.le
  have hu : (16 / T : ℝ) ^ 2 = 256 / T ^ 2 := by ring
  have hsbound : Real.sqrt (diagonalEnergy q (allocationAmplitude q x)) ≤ 16 / T := by
    nlinarith
  calc
    _ ≤ (1 + tailTotal q / q.mass 0) * Real.sqrt (diagonalEnergy q (allocationAmplitude q x)) :=
      likelihoodMatrix_frobenius_head_tail q (allocationAmplitude q x) hq
    _ ≤ (4 / 3 : ℝ) * Real.sqrt (diagonalEnergy q (allocationAmplitude q x)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hs0
    _ ≤ (4 / 3 : ℝ) * (16 / T) := mul_le_mul_of_nonneg_left hsbound (by norm_num)
    _ = _ := by ring

/-- Original `hh:signed-error`, for the actual heavy signed IID mixture. The
small universal constant is made explicit; the manuscript's c = 10⁻¹⁰ qualifies. -/
theorem allocation_heavy_signed_error
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR : tailTotal q ≤ (1 : ℝ) / 4) {T c : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) = 1)
    (hc0 : 0 ≤ c) (hcsmall : 64 * c / 3 ≤ 1 / 2) (n : ℕ) (hn : (n : ℝ) ≤ c * T) :
    FiniteTesting.totalVariation
      (mixture (uniformSigns k) (fun σ => productLaw
        (heavyLaw q (allocationAmplitude q x)
          (allocationAmplitude_bounds q x (fun i => (hx i).1)) hR σ) n))
      (productLaw q n) ≤ (1 / 2 : ℝ) * Real.sqrt (Real.exp ((64 * c / 3) ^ 2) - 1) := by
  let a := allocationAmplitude q x
  let ha := allocationAmplitude_bounds q x (fun i => (hx i).1)
  have hF := allocation_likelihoodMatrix_frobenius_bound q x hq hx hR hT hbudget
  have hnF : (n : ℝ) * frobeniusNorm (likelihoodMatrix q a) ≤ 64 * c / 3 := by
    calc
      _ ≤ (n : ℝ) * (64 / (3 * T)) := mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg n)
      _ ≤ (c * T) * (64 / (3 * T)) := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by field_simp
  have htv := signed_likelihood_matrix_totalVariation (heavyLaw q a ha hR) q
    (likelihoodMatrix q a) n (fun _ i hi => False.elim ((ne_of_gt (hq i)) hi))
    (heavyLaw_likelihoodInner_matrix q a ha hR hq) (hnF.trans hcsmall)
  have he : (n : ℝ) ^ 2 * frobeniusNorm (likelihoodMatrix q a) ^ 2 ≤ (64 * c / 3) ^ 2 := by
    have hs := pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg _)) hnF 2
    simpa only [mul_pow] using hs
  exact htv.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (sub_le_sub_right (Real.exp_le_exp.mpr he) 1)) (by norm_num))

end IdentityTesting.GeneralSignedMatrix
