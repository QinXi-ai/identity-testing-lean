import IdentityTesting.SignedDiagonalMoment
import IdentityTesting.AllocationAlgebra

/-!
# The actual heavy-head signed family

Tail signs are compensated at the head. The head lower bound, normalization,
tail displacement, and diagonal-plus-rank-one likelihood identity are derived
from the actual probability vectors.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavySignedFamily

open SignedDiagonalMoment

variable {k : ℕ}

def tailTotal (q : FiniteTesting.Probability (Fin (k + 1))) : ℝ := ∑ i : Fin k, q.mass i.succ

def signedSum (a : Fin k → ℝ) (σ : Fin k → Bool) : ℝ := ∑ i, a i * sign (σ i)

theorem reference_head_tail (q : FiniteTesting.Probability (Fin (k + 1))) :
    q.mass 0 + tailTotal q = 1 := by
  simpa only [Fin.sum_univ_succ, tailTotal] using q.total

def heavyMass (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (σ : Fin k → Bool) : Fin (k + 1) → ℝ :=
  Fin.cons (q.mass 0 - signedSum a σ) (fun i => q.mass i.succ + a i * sign (σ i))

@[simp] theorem heavyMass_head (q : FiniteTesting.Probability (Fin (k + 1)))
    (a : Fin k → ℝ) (σ : Fin k → Bool) :
    heavyMass q a σ 0 = q.mass 0 - signedSum a σ := rfl

@[simp] theorem heavyMass_tail (q : FiniteTesting.Probability (Fin (k + 1)))
    (a : Fin k → ℝ) (σ : Fin k → Bool) (i : Fin k) :
    heavyMass q a σ i.succ = q.mass i.succ + a i * sign (σ i) := by simp [heavyMass]

theorem signedSum_le (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i) (σ : Fin k → Bool) :
    signedSum a σ ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  cases hb : σ i <;> simp only [sign, mul_one, mul_neg_one] <;> linarith only [ha i]

theorem heavyMass_head_ge_half (q : FiniteTesting.Probability (Fin (k + 1)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ)
    (hR : tailTotal q ≤ (1 : ℝ) / 4) (σ : Fin k → Bool) :
    1 / 2 ≤ heavyMass q a σ 0 := by
  have hsign := signedSum_le a (fun i => (ha i).1) σ
  have hsum : (∑ i, a i) ≤ tailTotal q := Finset.sum_le_sum (fun i _ => (ha i).2)
  have htotal := reference_head_tail q
  rw [heavyMass_head]
  linarith only [hsign, hsum, hR, htotal]

theorem heavyMass_nonneg (q : FiniteTesting.Probability (Fin (k + 1)))
    (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ)
    (hR : tailTotal q ≤ (1 : ℝ) / 4) (σ : Fin k → Bool) (i : Fin (k + 1)) :
    0 ≤ heavyMass q a σ i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_trans (by norm_num) (heavyMass_head_ge_half q a ha hR σ)
  · rw [heavyMass_tail]
    cases hb : σ j <;> simp only [sign, mul_one, mul_neg_one] <;>
      linarith only [(ha j).1, (ha j).2, q.nonneg j.succ]

theorem heavyMass_total (q : FiniteTesting.Probability (Fin (k + 1)))
    (a : Fin k → ℝ) (σ : Fin k → Bool) : ∑ i, heavyMass q a σ i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [heavyMass_head, heavyMass_tail, Finset.sum_add_distrib]
  have hq := reference_head_tail q
  unfold tailTotal at hq
  unfold signedSum
  linarith only [hq]

def heavyLaw (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) : FiniteTesting.Probability (Fin (k + 1)) where
  mass := heavyMass q a σ
  nonneg := heavyMass_nonneg q a ha hR σ
  total := heavyMass_total q a σ

@[simp] theorem heavyLaw_mass_head (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) : (heavyLaw q a ha hR σ).mass 0 = q.mass 0 - signedSum a σ := rfl

@[simp] theorem heavyLaw_mass_tail (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) (i : Fin k) :
    (heavyLaw q a ha hR σ).mass i.succ = q.mass i.succ + a i * sign (σ i) := by
  exact heavyMass_tail q a σ i

theorem heavyLaw_totalVariation (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) :
    FiniteTesting.totalVariation (heavyLaw q a ha hR σ) q =
      (|signedSum a σ| + ∑ i, a i) / 2 := by
  have htail : ∀ i, |q.mass i.succ + a i * sign (σ i) - q.mass i.succ| = a i := by
    intro i
    have heq : q.mass i.succ + a i * sign (σ i) - q.mass i.succ = a i * sign (σ i) := by ring
    rw [heq]
    cases hb : σ i <;> simp [sign, abs_of_nonneg (ha i).1]
  have hhead : |q.mass 0 - signedSum a σ - q.mass 0| = |signedSum a σ| := by
    rw [show q.mass 0 - signedSum a σ - q.mass 0 = -signedSum a σ by ring, abs_neg]
  unfold FiniteTesting.totalVariation
  rw [Fin.sum_univ_succ]
  simp only [heavyLaw_mass_head, heavyLaw_mass_tail, hhead, htail]
  ring

theorem heavyLaw_totalVariation_ge (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) :
    (∑ i, a i) / 2 ≤ FiniteTesting.totalVariation (heavyLaw q a ha hR σ) q := by
  rw [heavyLaw_totalVariation]
  linarith only [abs_nonneg (signedSum a σ)]

private theorem head_likelihood_scalar (h A B : ℝ) (hh : h ≠ 0) :
    (h - A) * (h - B) / h = h - A - B + A * B / h := by
  field_simp [hh]
  ring

private theorem tail_likelihood_scalar (r a b c : ℝ) (hr : r ≠ 0) :
    (r + a * b) * (r + a * c) / r = r + a * b + a * c + (a ^ 2 / r) * b * c := by
  field_simp [hr]
  ring

/-- The actual matrix consists of the tail diagonal and the compensating-head
rank-one term. No likelihood relation is assumed about the constructed laws. -/
theorem heavyLaw_likelihoodInner (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hq : ∀ i, 0 < q.mass i) (σ τ : Fin k → Bool) :
    FiniteChiSquare.likelihoodInner (heavyLaw q a ha hR σ) (heavyLaw q a ha hR τ) q =
      1 + diagonalInteraction (fun i => a i ^ 2 / q.mass i.succ) σ τ +
        signedSum a σ * signedSum a τ / q.mass 0 := by
  unfold FiniteChiSquare.likelihoodInner
  rw [Fin.sum_univ_succ]
  simp only [heavyLaw_mass_head, heavyLaw_mass_tail]
  rw [head_likelihood_scalar _ _ _ (ne_of_gt (hq 0))]
  have htail : (∑ i, (q.mass i.succ + a i * sign (σ i)) *
      (q.mass i.succ + a i * sign (τ i)) / q.mass i.succ) =
      tailTotal q + signedSum a σ + signedSum a τ +
        diagonalInteraction (fun i => a i ^ 2 / q.mass i.succ) σ τ := by
    simp only [tail_likelihood_scalar _ _ _ _ (ne_of_gt (hq _)), Finset.sum_add_distrib,
      tailTotal, signedSum, diagonalInteraction]
  rw [htail]
  have htotal := reference_head_tail q
  linarith only [htotal]

def likelihoodMatrix (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (i j : Fin k) : ℝ :=
  (if i = j then a i ^ 2 / q.mass i.succ else 0) + a i * a j / q.mass 0

def matrixInteraction (M : Fin k → Fin k → ℝ) (σ τ : Fin k → Bool) : ℝ :=
  ∑ i, ∑ j, M i j * sign (σ i) * sign (τ j)

theorem matrixInteraction_likelihoodMatrix
    (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ) (σ τ : Fin k → Bool) :
    matrixInteraction (likelihoodMatrix q a) σ τ =
      diagonalInteraction (fun i => a i ^ 2 / q.mass i.succ) σ τ +
        signedSum a σ * signedSum a τ / q.mass 0 := by
  have hdiag : (∑ i, ∑ j,
      (if i = j then a i ^ 2 / q.mass i.succ else 0) * sign (σ i) * sign (τ j)) =
      diagonalInteraction (fun i => a i ^ 2 / q.mass i.succ) σ τ := by
    unfold diagonalInteraction
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul]
  have hrank : (∑ i, ∑ j, (a i * a j / q.mass 0) * sign (σ i) * sign (τ j)) =
      signedSum a σ * signedSum a τ / q.mass 0 := by
    unfold signedSum
    symm
    rw [Finset.sum_mul, Finset.sum_div]
    simp_rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold matrixInteraction likelihoodMatrix
  simp only [add_mul, Finset.sum_add_distrib]
  rw [hdiag, hrank]

theorem heavyLaw_likelihoodInner_matrix (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hq : ∀ i, 0 < q.mass i) (σ τ : Fin k → Bool) :
    FiniteChiSquare.likelihoodInner (heavyLaw q a ha hR σ) (heavyLaw q a ha hR τ) q =
      1 + matrixInteraction (likelihoodMatrix q a) σ τ := by
  rw [matrixInteraction_likelihoodMatrix, heavyLaw_likelihoodInner q a ha hR hq]
  ring

theorem uniformSigns_linear_mgf_le (a : Fin k → ℝ) (t : ℝ) :
    (∑ σ : Fin k → Bool, (uniformSigns k).mass σ * Real.exp (t * signedSum a σ)) ≤
      Real.exp (t ^ 2 * (∑ i, a i ^ 2) / 2) := by
  calc
    _ = ∏ i, Real.cosh (t * a i) := by
      simpa only [signedSum, Finset.mul_sum, mul_assoc] using
        uniformSigns_mgf (fun i => t * a i)
    _ ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 2) :=
      Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (∑ i, (t * a i) ^ 2 / 2) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

def allocationAmplitude (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  if x i ≤ (1 : ℝ) / 4 then 4 * q.mass i.succ * x i else 0

theorem allocationAmplitude_bounds (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i : Fin k) :
    0 ≤ allocationAmplitude q x i ∧ allocationAmplitude q x i ≤ q.mass i.succ := by
  unfold allocationAmplitude
  split_ifs with h
  · have hm := mul_le_mul_of_nonneg_left h (q.nonneg i.succ)
    exact ⟨mul_nonneg (mul_nonneg (by norm_num) (q.nonneg _)) (hx i), by nlinarith only [hm]⟩
  · exact ⟨le_rfl, q.nonneg _⟩

theorem allocationAmplitude_sum (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ) :
    (∑ i, allocationAmplitude q x i) =
      4 * ∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4), q.mass i.succ * x i := by
  rw [Finset.mul_sum]
  simp only [allocationAmplitude, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

end IdentityTesting.HeavySignedFamily
