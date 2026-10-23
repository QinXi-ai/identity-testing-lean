import IdentityTesting.EventCountMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual fixed-sample weighted quadratic statistics for the full-prefix tester.
The mean is derived from the sample law; no testing or variance bound is assumed.
This module supplies the moment identities used by the profile tester. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def labelCentered (q : Probability Ω) (x y : Ω) : ℝ :=
  (if y = x then 1 else 0) - q.mass x

def weightedSignal (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) : ℝ :=
  ∑ x ∈ H, (p.mass x - q.mass x) ^ 2 / w x

def weightedKernel (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) (x y : Ω) : ℝ :=
  ∑ z ∈ H, labelCentered q z x * labelCentered q z y / w z

def weightedStatistic (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (n : ℕ) (sample : Fin n → Ω) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i, weightedKernel q H w (sample i) (sample j)) /
    ((n : ℝ) * ((n : ℝ) - 1))

theorem mean_labelCentered (p q : Probability Ω) (x : Ω) :
    mean p (labelCentered q x) = p.mass x - q.mass x := by
  unfold labelCentered
  rw [mean_sub, mean_const]
  simp [mean, mul_ite]

theorem mean_weightedKernel (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    mean (productLaw p n) (fun sample => weightedKernel q H w (sample i) (sample j)) =
      weightedSignal p q H w := by
  unfold weightedKernel weightedSignal
  rw [mean_finset_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [mean_div_const, mean_productLaw_two_coordinates p n i j hij,
    mean_labelCentered]
  ring

theorem mean_weightedStatistic (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (n : ℕ) (hn : 2 ≤ n) :
    mean (productLaw p n) (weightedStatistic q H w n) = weightedSignal p q H w := by
  have hnR : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa using (Nat.cast_sub (R := ℝ) (show (1 : ℕ) ≤ n by omega))
  unfold weightedStatistic
  rw [mean_div_const, mean_finset_sum]
  have hinner : ∀ i : Fin n,
      mean (productLaw p n) (fun sample => ∑ j ∈ Finset.univ.erase i,
        weightedKernel q H w (sample i) (sample j)) =
        ((n : ℝ) - 1) * weightedSignal p q H w := by
    intro i
    rw [mean_finset_sum]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, weightedSignal p q H w := by
        apply Finset.sum_congr rfl
        intro j hj
        exact mean_weightedKernel p q H w n i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by simp [Finset.card_erase_of_mem, hcard]
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [DecidableEq Ω] in
theorem weightedSignal_nonneg (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ x ∈ H, 0 ≤ w x) : 0 ≤ weightedSignal p q H w := by
  exact Finset.sum_nonneg (fun x hx => div_nonneg (sq_nonneg _) (hw x hx))

omit [DecidableEq Ω] in
theorem weightedSignal_null (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) :
    weightedSignal q q H w = 0 := by simp [weightedSignal]

omit [DecidableEq Ω] in
theorem weighted_discrepancy_sq_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ x ∈ H, 0 < w x) :
    (∑ x ∈ H, |p.mass x - q.mass x|) ^ 2 ≤
      weightedSignal p q H w * ∑ x ∈ H, w x := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul H
    (fun x hx => div_nonneg (sq_nonneg _) (hw x hx).le) (fun x hx => (hw x hx).le)
  intro x hx
  rw [sq_abs]
  exact (div_mul_cancel₀ _ (ne_of_gt (hw x hx))).symm

end IdentityTesting.ProfileTesting
