import IdentityTesting.ProfileTestingMoments
import IdentityTesting.ProfileScalarMoments
import IdentityTesting.ProfileSampleSplit

/-! The actual two-batch weighted statistic and its conditional second moments. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def crossStatistic (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (left : Fin m → Ω) (right : Fin n → Ω) : ℝ :=
  ∑ i ∈ H, empiricalMean (labelCentered q i) m left *
    empiricalMean (labelCentered q i) n right / w i

def signalProjection (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) : Ω → ℝ :=
  shiftedLabelLinear q H (fun i => (p.mass i - q.mass i) / w i)

def varianceLinearTerm (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) : ℝ :=
  ∑ i ∈ H, p.mass i * (p.mass i - q.mass i) ^ 2 / w i ^ 2

def varianceQuadraticTerm (p : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) : ℝ :=
  ∑ i ∈ H, p.mass i ^ 2 / w i ^ 2

omit [Fintype Ω] [DecidableEq Ω] in
theorem empiricalMean_finset_sum {I : Type*} (s : Finset I) (f : I → Ω → ℝ)
    (n : ℕ) (sample : Fin n → Ω) :
    empiricalMean (fun x => ∑ i ∈ s, f i x) n sample =
      ∑ i ∈ s, empiricalMean (f i) n sample := by
  unfold empiricalMean
  rw [Finset.sum_comm, Finset.sum_div]

omit [Fintype Ω] [DecidableEq Ω] in
theorem empiricalMean_const_mul (c : ℝ) (f : Ω → ℝ) (n : ℕ) (sample : Fin n → Ω) :
    empiricalMean (fun x => c * f x) n sample = c * empiricalMean f n sample := by
  simp only [empiricalMean, ← Finset.mul_sum]
  ring

theorem empiricalMean_shiftedLabelLinear (q : Probability Ω) (H : Finset Ω) (c : Ω → ℝ)
    (n : ℕ) (sample : Fin n → Ω) :
    empiricalMean (shiftedLabelLinear q H c) n sample =
      ∑ i ∈ H, c i * empiricalMean (labelCentered q i) n sample := by
  unfold shiftedLabelLinear
  rw [empiricalMean_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact empiricalMean_const_mul (c i) (labelCentered q i) n sample

theorem crossStatistic_as_rightMean (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (left : Fin m → Ω) (right : Fin n → Ω) :
    crossStatistic q H w m n left right =
      empiricalMean (shiftedLabelLinear q H
        (fun i => empiricalMean (labelCentered q i) m left / w i)) n right := by
  rw [empiricalMean_shiftedLabelLinear]
  unfold crossStatistic
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cross_conditionalMean (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m : ℕ) (left : Fin m → Ω) :
    mean p (shiftedLabelLinear q H
      (fun i => empiricalMean (labelCentered q i) m left / w i)) =
        empiricalMean (signalProjection p q H w) m left := by
  rw [mean_shiftedLabelLinear]
  unfold signalProjection
  rw [empiricalMean_shiftedLabelLinear]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mean_signalProjection (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) :
    mean p (signalProjection p q H w) = weightedSignal p q H w := by
  unfold signalProjection
  rw [mean_shiftedLabelLinear]
  unfold weightedSignal
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem variance_signalProjection_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ) :
    scalarVariance p (signalProjection p q H w) ≤ varianceLinearTerm p q H w := by
  have h := scalarVariance_shiftedLabelLinear_le p q H (fun i => (p.mass i - q.mass i) / w i)
  simpa only [signalProjection, varianceLinearTerm, div_pow, mul_div_assoc] using h

theorem mean_crossStatistic_right (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hn : 0 < n) (left : Fin m → Ω) :
    mean (productLaw p n) (crossStatistic q H w m n left) =
      empiricalMean (signalProjection p q H w) m left := by
  have hf : crossStatistic q H w m n left =
      empiricalMean (shiftedLabelLinear q H
        (fun i => empiricalMean (labelCentered q i) m left / w i)) n := by
    funext right
    exact crossStatistic_as_rightMean q H w m n left right
  rw [hf, mean_empiricalMean p _ n hn, cross_conditionalMean]

theorem mean_crossStatistic (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    mean (productLaw p m) (fun left => mean (productLaw p n) (crossStatistic q H w m n left)) =
      weightedSignal p q H w := by
  simp only [mean_crossStatistic_right p q H w m n hn,
    mean_empiricalMean p _ m hm, mean_signalProjection]

theorem scalarVariance_labelCentered_le (p q : Probability Ω) (i : Ω) :
    scalarVariance p (labelCentered q i) ≤ p.mass i := by
  have hf : labelCentered q i = (fun y => labelLinear {i} (fun _ => 1) y - q.mass i) := by
    funext y
    simp [labelCentered, labelLinear]
  rw [hf, scalarVariance_sub_const]
  simpa using scalarVariance_labelLinear_le p {i} (fun _ => 1)

theorem mean_empirical_labelCentered_sq_le (p q : Probability Ω) (i : Ω)
    (m : ℕ) (hm : 0 < m) :
    mean (productLaw p m) (fun left => empiricalMean (labelCentered q i) m left ^ 2) ≤
      (p.mass i - q.mass i) ^ 2 + p.mass i / m := by
  rw [mean_empiricalMean_sq p _ m hm, mean_labelCentered]
  exact add_le_add_left
    (div_le_div_of_nonneg_right (scalarVariance_labelCentered_le p q i) (Nat.cast_nonneg m)) _

theorem cross_conditional_secondMoment_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hn : 0 < n) (left : Fin m → Ω) :
    mean (productLaw p n) (fun right => crossStatistic q H w m n left right ^ 2) ≤
      empiricalMean (signalProjection p q H w) m left ^ 2 +
        (∑ i ∈ H, p.mass i * empiricalMean (labelCentered q i) m left ^ 2 / w i ^ 2) / n := by
  have hf : (fun right => crossStatistic q H w m n left right ^ 2) =
      (fun right => empiricalMean (shiftedLabelLinear q H
        (fun i => empiricalMean (labelCentered q i) m left / w i)) n right ^ 2) := by
    funext right
    rw [crossStatistic_as_rightMean]
  rw [hf, mean_empiricalMean_sq p _ n hn, cross_conditionalMean]
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  simpa only [div_pow, mul_div_assoc] using scalarVariance_shiftedLabelLinear_le p q H
    (fun i => empiricalMean (labelCentered q i) m left / w i)

theorem mean_cross_coefficients_sq_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m : ℕ) (hm : 0 < m) :
    mean (productLaw p m) (fun left =>
      ∑ i ∈ H, p.mass i * empiricalMean (labelCentered q i) m left ^ 2 / w i ^ 2) ≤
        varianceLinearTerm p q H w + varianceQuadraticTerm p H w / m := by
  rw [mean_finset_sum]
  calc
    _ ≤ ∑ i ∈ H, p.mass i * ((p.mass i - q.mass i) ^ 2 + p.mass i / m) / w i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [mean_div_const, mean_const_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mean_empirical_labelCentered_sq_le p q i m hm) (p.nonneg i))
        (sq_nonneg _)
    _ = _ := by
      unfold varianceLinearTerm varianceQuadraticTerm
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem cross_secondMoment_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    mean (productLaw p m) (fun left =>
      mean (productLaw p n) (fun right => crossStatistic q H w m n left right ^ 2)) ≤
        weightedSignal p q H w ^ 2 + varianceLinearTerm p q H w / m +
          varianceLinearTerm p q H w / n + varianceQuadraticTerm p H w / ((m : ℝ) * n) := by
  calc
    _ ≤ mean (productLaw p m) (fun left =>
        empiricalMean (signalProjection p q H w) m left ^ 2 +
          (∑ i ∈ H, p.mass i * empiricalMean (labelCentered q i) m left ^ 2 / w i ^ 2) / n) :=
      mean_mono _ (cross_conditional_secondMoment_le p q H w m n hn)
    _ = mean (productLaw p m) (fun left => empiricalMean (signalProjection p q H w) m left ^ 2) +
        mean (productLaw p m) (fun left =>
          ∑ i ∈ H, p.mass i * empiricalMean (labelCentered q i) m left ^ 2 / w i ^ 2) / n := by
      rw [mean_add, mean_div_const]
    _ ≤ (weightedSignal p q H w ^ 2 + varianceLinearTerm p q H w / m) +
        (varianceLinearTerm p q H w + varianceQuadraticTerm p H w / m) / n := by
      apply add_le_add
      · rw [mean_empiricalMean_sq p _ m hm, mean_signalProjection]
        exact add_le_add_left (div_le_div_of_nonneg_right
          (variance_signalProjection_le p q H w) (Nat.cast_nonneg m)) _
      · exact div_le_div_of_nonneg_right (mean_cross_coefficients_sq_le p q H w m hm)
          (Nat.cast_nonneg n)
    _ = _ := by ring

def fixedCrossStatistic (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (sample : Fin (m + n) → Ω) : ℝ :=
  crossStatistic q H w m n (firstBlock m n sample) (secondBlock m n sample)

theorem mean_fixedCrossStatistic (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    mean (productLaw p (m + n)) (fixedCrossStatistic q H w m n) = weightedSignal p q H w := by
  unfold fixedCrossStatistic
  rw [mean_productLaw_blocks p m n (crossStatistic q H w m n), mean_crossStatistic p q H w m n hm hn]

theorem variance_fixedCrossStatistic_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    scalarVariance (productLaw p (m + n)) (fixedCrossStatistic q H w m n) ≤
      varianceLinearTerm p q H w / m + varianceLinearTerm p q H w / n +
        varianceQuadraticTerm p H w / ((m : ℝ) * n) := by
  rw [scalarVariance_eq, mean_fixedCrossStatistic p q H w m n hm hn]
  have hsecond := cross_secondMoment_le p q H w m n hm hn
  have heq : mean (productLaw p (m + n)) (fun sample => fixedCrossStatistic q H w m n sample ^ 2) =
      mean (productLaw p m) (fun left => mean (productLaw p n)
        (fun right => crossStatistic q H w m n left right ^ 2)) :=
    mean_productLaw_blocks p m n (fun left right => crossStatistic q H w m n left right ^ 2)
  rw [heq]
  linarith

end IdentityTesting.ProfileTesting
