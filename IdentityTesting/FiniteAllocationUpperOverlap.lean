import IdentityTesting.FiniteAllocationUpperMean

/-! Small actual overlap forces a large collision signal unless the actual
weighted mean is already separated. No testing-success premise is assumed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID ProfileTesting CollisionTesting

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def localOverlap (p q : Probability Ω) (L : Finset Ω) : ℝ :=
  ∑ i ∈ L, min (p.mass i) (q.mass i)

def excessLabels (p q : Probability Ω) (L : Finset Ω) : Finset Ω :=
  L.filter (fun i => q.mass i < p.mass i)

omit [DecidableEq Ω] in
theorem excess_reference_mass_le_overlap (p q : Probability Ω) (L : Finset Ω) :
    (∑ i ∈ excessLabels p q L, q.mass i) ≤ localOverlap p q L := by
  classical
  rw [excessLabels, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i hi
  split
  · rename_i h
    rw [min_eq_right h.le]
  · exact le_min (p.nonneg i) (q.nonneg i)

omit [DecidableEq Ω] in
theorem weightedMass_le_excess_add_overlap (p q : Probability Ω) (L : Finset Ω)
    (w : ℝ) (hw0 : 0 ≤ w) (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w) :
    weightedMass p q L ≤ weightedMass p q (excessLabels p q L) + w * localOverlap p q L := by
  classical
  unfold weightedMass localOverlap excessLabels
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : q.mass i < p.mass i
  · rw [if_pos h]
    exact le_add_of_nonneg_right (mul_nonneg hw0 (le_min (p.nonneg i) (q.nonneg i)))
  · rw [if_neg h, zero_add, min_eq_left (le_of_not_gt h)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hw i hi) (p.nonneg i)

omit [DecidableEq Ω] in
theorem weightedMass_excess_sq_le (p q : Probability Ω) (L : Finset Ω) :
    weightedMass p q (excessLabels p q L) ^ 2 ≤
      collisionMass2 p L * localOverlap p q L := by
  let J := excessLabels p q L
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul J
    (r := fun i => p.mass i * Real.sqrt (q.mass i))
    (f := fun i => p.mass i ^ 2) (g := q.mass)
    (fun i _ => sq_nonneg _) (fun i _ => q.nonneg i) (by
      intro i hi
      rw [mul_pow, Real.sq_sqrt (q.nonneg i)])
  have hs : (∑ i ∈ J, p.mass i ^ 2) ≤ collisionMass2 p L := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro i hi hj
      exact sq_nonneg _
  have hq := excess_reference_mass_le_overlap p q L
  have h0 : 0 ≤ ∑ i ∈ J, q.mass i := Finset.sum_nonneg (fun i _ => q.nonneg i)
  have hsig : 0 ≤ collisionMass2 p L := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  exact hc.trans (mul_le_mul hs hq h0 hsig)

omit [DecidableEq Ω] in
theorem collision_signal_of_small_overlap (p q : Probability Ω) (L : Finset Ω)
    (w E : ℝ) (hw0 : 0 ≤ w) (hE : 0 < E) (hA : 0 < weightedMass q q L)
    (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w)
    (hsmall : 8 * w * E ≤ weightedMass q q L)
    (hoverlap : localOverlap p q L ≤ 2 * E)
    (hmean : weightedMass q q L / 2 < weightedMass p q L) :
    weightedMass q q L ^ 2 / (32 * E) ≤ collisionMass2 p L := by
  have hdecomp := weightedMass_le_excess_add_overlap p q L w hw0 hw
  have hwo := mul_le_mul_of_nonneg_left hoverlap hw0
  have hJ : weightedMass q q L / 4 < weightedMass p q (excessLabels p q L) := by
    linarith
  have hJ0 := weightedMass_nonneg p q (excessLabels p q L)
  have hc := weightedMass_excess_sq_le p q L
  have hsig : 0 ≤ collisionMass2 p L := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc' := mul_le_mul_of_nonneg_left hoverlap hsig
  apply (div_le_iff₀ (by positivity : 0 < 32 * E)).2
  have hsq : (weightedMass q q L / 4) ^ 2 ≤
      weightedMass p q (excessLabels p q L) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hJ.le 2
  nlinarith only [hsq, hc, hc']

def weightedMeanRepeatTest (q : Probability Ω) (L : Finset Ω) (n : ℕ) :
    RandomizedTest (Fin n → Ω) :=
  testMaximum (weightedMeanTest q L n) (repeatTest L n)

theorem weightedMeanRepeatTest_null_error (q : Probability Ω) (L : Finset Ω)
    (n : ℕ) (w : ℝ) (hn : 0 < n) (hA : 0 < weightedMass q q L)
    (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w)
    (hmean : 200 * w ≤ (n : ℝ) * weightedMass q q L)
    (hcollision : (n : ℝ) ^ 2 * collisionMass2 q L ≤ 1 / 100) :
    expectation (productLaw q n) (weightedMeanRepeatTest q L n) ≤ 1 / 10 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm := weightedMeanTest_null_error q L n w hn hA hw
  have hm' : 16 * w / ((n : ℝ) * weightedMass q q L) ≤ 2 / 25 := by
    apply (div_le_iff₀ (mul_pos hnR hA)).2
    linarith
  have hc := repeat_probability_le q L n
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [sq_nonneg (n : ℝ)]
  have hc' := mul_le_mul_of_nonneg_right hchoose
    (Finset.sum_nonneg (fun i _ => sq_nonneg (q.mass i)) : 0 ≤ collisionMass2 q L)
  have hu := expectation_testMaximum_le (productLaw q n)
    (weightedMeanTest q L n) (repeatTest L n)
  change expectation (productLaw q n) (testMaximum _ _) ≤ _
  dsimp [collisionMass2] at hcollision
  linarith

theorem repeatTest_miss_of_signal (p : Probability Ω) (L : Finset Ω) (n : ℕ)
    (hn : 2 ≤ n) (hsignal : 1000000 ≤ (n : ℝ) ^ 2 * collisionMass2 p L) :
    1 - expectation (productLaw p n) (repeatTest L n) ≤ 1 / 50 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp2 : 0 < collisionMass2 p L := by
    by_contra h
    have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (n : ℝ)) (le_of_not_gt h)
    linarith
  have hs := Real.sq_sqrt hp2.le
  have hs0 := Real.sqrt_nonneg (collisionMass2 p L)
  have hden : 1000 ≤ (n : ℝ) * Real.sqrt (collisionMass2 p L) := by
    have heq : ((n : ℝ) * Real.sqrt (collisionMass2 p L)) ^ 2 =
        (n : ℝ) ^ 2 * collisionMass2 p L := by rw [mul_pow, hs]
    nlinarith [mul_nonneg hnR.le hs0]
  have hfirst : 4 / ((n : ℝ) ^ 2 * collisionMass2 p L) ≤ 4 / 1000000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsignal
  have hsecond : 16 / ((n : ℝ) * Real.sqrt (collisionMass2 p L)) ≤ 16 / 1000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  have hc := no_repeat_probability_le p L n hn hp2
  linarith

theorem weightedMeanRepeatTest_alternative_error (p q : Probability Ω) (L : Finset Ω)
    (n : ℕ) (w E : ℝ) (hn : 2 ≤ n) (hw0 : 0 ≤ w) (hE : 0 < E)
    (hA : 0 < weightedMass q q L)
    (hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ w)
    (hmean : 200 * w ≤ (n : ℝ) * weightedMass q q L)
    (hsmall : 8 * w * E ≤ weightedMass q q L)
    (hoverlap : localOverlap p q L ≤ 2 * E)
    (hscale : 32000000 * E ≤ (n : ℝ) ^ 2 * weightedMass q q L ^ 2) :
    1 - expectation (productLaw p n) (weightedMeanRepeatTest q L n) ≤ 1 / 20 := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  by_cases hsep : weightedMass p q L ≤ weightedMass q q L / 2
  · have hm := weightedMeanTest_alternative_error p q L n w hn0 hA hw0 hw hsep
    have hb : 8 * w / ((n : ℝ) * weightedMass q q L) ≤ 1 / 25 := by
      apply (div_le_iff₀ (mul_pos hnR hA)).2
      linarith
    have hdom := expectation_le_testMaximum_left (productLaw p n)
      (weightedMeanTest q L n) (repeatTest L n)
    change 1 - expectation (productLaw p n) (testMaximum _ _) ≤ _
    linarith
  · have hs := collision_signal_of_small_overlap p q L w E hw0 hE hA hw hsmall
      hoverlap (lt_of_not_ge hsep)
    have hs' := (div_le_iff₀ (by positivity : 0 < 32 * E)).mp hs
    have hscaled := mul_le_mul_of_nonneg_left hs' (sq_nonneg (n : ℝ))
    have hsignal : 1000000 ≤ (n : ℝ) ^ 2 * collisionMass2 p L := by
      have hprod : 32000000 * E ≤ ((n : ℝ) ^ 2 * collisionMass2 p L * 32) * E := by
        convert hscale.trans hscaled using 1
        ring
      have hc := (mul_le_mul_iff_left₀ hE).mp hprod
      linarith
    have hc := repeatTest_miss_of_signal p L n hn hsignal
    have hdom := expectation_le_testMaximum_right (productLaw p n)
      (weightedMeanTest q L n) (repeatTest L n)
    change 1 - expectation (productLaw p n) (testMaximum _ _) ≤ _
    linarith

end IdentityTesting.FiniteAllocationUpper
