import IdentityTesting.ProfileTesting
import IdentityTesting.CollisionDetection

/-! Actual weighted empirical-mean tests for the finite allocation upper bound.
All moments below are evaluated under the finite IID product law. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID ProfileTesting CollisionTesting EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def weightedObservation (q : Probability Ω) (L : Finset Ω) : Ω → ℝ :=
  labelLinear L (fun i => Real.sqrt (q.mass i))

def weightedMass (p q : Probability Ω) (L : Finset Ω) : ℝ :=
  ∑ i ∈ L, p.mass i * Real.sqrt (q.mass i)

theorem mean_weightedObservation (p q : Probability Ω) (L : Finset Ω) :
    mean p (weightedObservation q L) = weightedMass p q L := by
  classical
  simp [mean, weightedObservation, labelLinear, weightedMass, mul_ite]

omit [DecidableEq Ω] in
theorem weightedMass_nonneg (p q : Probability Ω) (L : Finset Ω) :
    0 ≤ weightedMass p q L :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (p.nonneg i) (Real.sqrt_nonneg _))

theorem variance_weightedObservation_le (p q : Probability Ω) (L : Finset Ω)
    (w : ℝ) (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) :
    scalarVariance p (weightedObservation q L) ≤ w * weightedMass p q L := by
  calc
    _ ≤ ∑ i ∈ L, p.mass i * Real.sqrt (q.mass i) ^ 2 :=
      scalarVariance_labelLinear_le p L _
    _ ≤ ∑ i ∈ L, w * (p.mass i * Real.sqrt (q.mass i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_left (hw i hi)
        (mul_nonneg (p.nonneg i) (Real.sqrt_nonneg (q.mass i)))
      nlinarith only [h]
    _ = _ := (Finset.mul_sum _ _ _).symm

def weightedMeanTest (q : Probability Ω) (L : Finset Ω) (n : ℕ) :
    RandomizedTest (Fin n → Ω) where
  reject sample := if empiricalMean (weightedObservation q L) n sample <
      3 * weightedMass q q L / 4 then 1 else 0
  nonneg _ := by split <;> norm_num
  le_one _ := by split <;> norm_num

theorem weightedMeanTest_null_error (q : Probability Ω) (L : Finset Ω)
    (n : ℕ) (w : ℝ) (hn : 0 < n) (hA : 0 < weightedMass q q L)
    (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) :
    expectation (productLaw q n) (weightedMeanTest q L n) ≤
      16 * w / ((n : ℝ) * weightedMass q q L) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < weightedMass q q L / 4 := by positivity
  have hmean := mean_empiricalMean q (weightedObservation q L) n hn
  rw [mean_weightedObservation] at hmean
  have hv := variance_weightedObservation_le q q L w hw
  have htail := scalar_event_probability_le (productLaw q n)
    (empiricalMean (weightedObservation q L) n) (weightedMass q q L / 4) ht
    (fun sample => empiricalMean (weightedObservation q L) n sample <
      3 * weightedMass q q L / 4) (by
        intro sample hs
        rw [hmean]
        have habs := neg_le_abs (empiricalMean (weightedObservation q L) n sample -
          weightedMass q q L)
        linarith)
  change mean (productLaw q n) (fun sample => if
    empiricalMean (weightedObservation q L) n sample < 3 * weightedMass q q L / 4
      then 1 else 0) ≤ _
  apply htail.trans
  rw [scalarVariance_empiricalMean q _ n hn]
  calc
    _ ≤ (w * weightedMass q q L / (n : ℝ)) / (weightedMass q q L / 4) ^ 2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hv hnR.le) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem weightedMeanTest_alternative_error (p q : Probability Ω) (L : Finset Ω)
    (n : ℕ) (w : ℝ) (hn : 0 < n) (hA : 0 < weightedMass q q L)
    (hw0 : 0 ≤ w) (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w)
    (hsep : weightedMass p q L ≤ weightedMass q q L / 2) :
    1 - expectation (productLaw p n) (weightedMeanTest q L n) ≤
      8 * w / ((n : ℝ) * weightedMass q q L) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ht : 0 < weightedMass q q L / 4 := by positivity
  have hmean := mean_empiricalMean p (weightedObservation q L) n hn
  rw [mean_weightedObservation] at hmean
  have hv := (variance_weightedObservation_le p q L w hw).trans
    (mul_le_mul_of_nonneg_left hsep hw0)
  have htail := scalar_event_probability_le (productLaw p n)
    (empiricalMean (weightedObservation q L) n) (weightedMass q q L / 4) ht
    (fun sample => 3 * weightedMass q q L / 4 ≤
      empiricalMean (weightedObservation q L) n sample) (by
        intro sample hs
        rw [hmean]
        have habs := le_abs_self (empiricalMean (weightedObservation q L) n sample -
          weightedMass p q L)
        linarith)
  have hmiss : 1 - expectation (productLaw p n) (weightedMeanTest q L n) =
      mean (productLaw p n) (fun sample => if 3 * weightedMass q q L / 4 ≤
        empiricalMean (weightedObservation q L) n sample then 1 else 0) := by
    have hf : (fun sample => 1 - (weightedMeanTest q L n).reject sample) =
        (fun sample => if 3 * weightedMass q q L / 4 ≤
          empiricalMean (weightedObservation q L) n sample then (1 : ℝ) else 0) := by
      funext sample
      dsimp [weightedMeanTest]
      split <;> simp_all only [not_le, not_lt, if_pos, if_neg] <;> norm_num
    rw [← hf, mean_sub, mean_const]
    rfl
  rw [hmiss]
  apply htail.trans
  rw [scalarVariance_empiricalMean p _ n hn]
  calc
    _ ≤ (w * (weightedMass q q L / 2) / (n : ℝ)) /
        (weightedMass q q L / 4) ^ 2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hv hnR.le) (sq_nonneg _)
    _ = _ := by field_simp; ring

end IdentityTesting.FiniteAllocationUpper
