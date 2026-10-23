import IdentityTesting.EventCountMoments

/-! Scalar empirical-mean moments used to prove the two-batch profile test's
conditional second-moment bound from actual IID observations. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω]

def scalarVariance (p : Probability Ω) (f : Ω → ℝ) : ℝ :=
  mean p (fun x => (f x - mean p f) ^ 2)

def empiricalMean (f : Ω → ℝ) (n : ℕ) (sample : Fin n → Ω) : ℝ :=
  (∑ j, f (sample j)) / n

theorem mean_const_mul (p : Probability Ω) (c : ℝ) (f : Ω → ℝ) :
    mean p (fun x => c * f x) = c * mean p f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem scalarVariance_nonneg (p : Probability Ω) (f : Ω → ℝ) :
    0 ≤ scalarVariance p f := mean_nonneg _ (fun _ => sq_nonneg _)

theorem scalarVariance_eq (p : Probability Ω) (f : Ω → ℝ) :
    scalarVariance p f = mean p (fun x => f x ^ 2) - (mean p f) ^ 2 := by
  have hfun : (fun x => (f x - mean p f) ^ 2) =
      (fun x => f x ^ 2 - f x * (2 * mean p f) + (mean p f) ^ 2) := by
    funext x
    ring
  unfold scalarVariance
  rw [hfun, mean_add, mean_sub, mean_mul_const, mean_const]
  ring

theorem scalarVariance_sub_const (p : Probability Ω) (f : Ω → ℝ) (c : ℝ) :
    scalarVariance p (fun x => f x - c) = scalarVariance p f := by
  unfold scalarVariance
  rw [mean_sub, mean_const]
  congr 1
  funext x
  ring

theorem mean_empiricalMean (p : Probability Ω) (f : Ω → ℝ) (n : ℕ) (hn : 0 < n) :
    mean (productLaw p n) (empiricalMean f n) = mean p f := by
  unfold empiricalMean
  rw [mean_div_const, mean_finset_sum]
  simp [mean_productLaw_coordinate, Nat.ne_of_gt hn]

theorem scalarVariance_empiricalMean (p : Probability Ω) (f : Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    scalarVariance (productLaw p n) (empiricalMean f n) = scalarVariance p f / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hg : mean p (fun x => f x - mean p f) = 0 := by
    rw [mean_sub, mean_const, sub_self]
  have hfun : (fun sample : Fin n → Ω => (empiricalMean f n sample - mean p f) ^ 2) =
      (fun sample => (∑ j, (f (sample j) - mean p f)) ^ 2 / (n : ℝ) ^ 2) := by
    funext sample
    simp only [empiricalMean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  unfold scalarVariance
  rw [mean_empiricalMean p f n hn, hfun, mean_div_const, mean_centered_sum_sq p n _ hg]
  field_simp

theorem mean_empiricalMean_sq (p : Probability Ω) (f : Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    mean (productLaw p n) (fun sample => empiricalMean f n sample ^ 2) =
      (mean p f) ^ 2 + scalarVariance p f / n := by
  have hv := scalarVariance_empiricalMean p f n hn
  rw [scalarVariance_eq, mean_empiricalMean p f n hn] at hv
  linarith

theorem mean_square_sub_const (p : Probability Ω) (f : Ω → ℝ) (c : ℝ) :
    mean p (fun x => (f x - c) ^ 2) = scalarVariance p f + (mean p f - c) ^ 2 := by
  have hfun : (fun x => (f x - c) ^ 2) =
      (fun x => f x ^ 2 - f x * (2 * c) + c ^ 2) := by
    funext x
    ring
  rw [hfun, mean_add, mean_sub, mean_mul_const, mean_const, scalarVariance_eq]
  ring

theorem empiricalMean_mse (p : Probability Ω) (f : Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (c : ℝ) :
    mean (productLaw p n) (fun sample => (empiricalMean f n sample - c) ^ 2) =
      scalarVariance p f / n + (mean p f - c) ^ 2 := by
  rw [mean_square_sub_const, scalarVariance_empiricalMean p f n hn,
    mean_empiricalMean p f n hn]

variable [DecidableEq Ω]

def labelLinear (H : Finset Ω) (c : Ω → ℝ) (x : Ω) : ℝ := if x ∈ H then c x else 0

theorem mean_labelLinear_sq (p : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) :
    mean p (fun x => labelLinear H c x ^ 2) = ∑ x ∈ H, p.mass x * c x ^ 2 := by
  classical
  simp [mean, labelLinear, ite_pow, mul_ite]

theorem scalarVariance_labelLinear_le (p : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) :
    scalarVariance p (labelLinear H c) ≤ ∑ x ∈ H, p.mass x * c x ^ 2 := by
  rw [scalarVariance_eq, mean_labelLinear_sq]
  exact sub_le_self _ (sq_nonneg _)

def shiftedLabelLinear (q : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) (y : Ω) : ℝ :=
  ∑ x ∈ H, c x * ((if y = x then 1 else 0) - q.mass x)

theorem shiftedLabelLinear_eq (q : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) (y : Ω) :
    shiftedLabelLinear q H c y = labelLinear H c y - ∑ x ∈ H, c x * q.mass x := by
  classical
  simp [shiftedLabelLinear, labelLinear, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem scalarVariance_shiftedLabelLinear_le (p q : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) :
    scalarVariance p (shiftedLabelLinear q H c) ≤ ∑ x ∈ H, p.mass x * c x ^ 2 := by
  have hfun : shiftedLabelLinear q H c =
      (fun y => labelLinear H c y - ∑ x ∈ H, c x * q.mass x) := by
    funext y
    exact shiftedLabelLinear_eq q H c y
  rw [hfun, scalarVariance_sub_const]
  exact scalarVariance_labelLinear_le p H c

theorem mean_shiftedLabelLinear (p q : Probability Ω) (H : Finset Ω) (c : Ω → ℝ) :
    mean p (shiftedLabelLinear q H c) = ∑ x ∈ H, c x * (p.mass x - q.mass x) := by
  unfold shiftedLabelLinear
  rw [mean_finset_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [mean_const_mul, mean_sub, mean_const]
  simp [mean, mul_ite]

end IdentityTesting.ProfileTesting
