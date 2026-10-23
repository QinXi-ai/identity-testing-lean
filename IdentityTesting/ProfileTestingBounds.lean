import IdentityTesting.ProfileTestingCrossMoments

/-! Quantitative regular-weight bounds and actual two-batch quadratic tests. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem scalar_event_probability_le (p : Probability Ω) (f : Ω → ℝ)
    (t : ℝ) (ht : 0 < t) (B : Ω → Prop) [DecidablePred B]
    (hB : ∀ x, B x → t ≤ |f x - mean p f|) :
    mean p (fun x => if B x then 1 else 0) ≤ scalarVariance p f / t ^ 2 := by
  have hpoint : ∀ x, (if B x then (1 : ℝ) else 0) ≤ (f x - mean p f) ^ 2 / t ^ 2 := by
    intro x
    by_cases hx : B x
    · rw [if_pos hx]
      apply (le_div_iff₀ (sq_pos_of_pos ht)).2
      have h := mul_self_le_mul_self ht.le (hB x hx)
      simpa [← pow_two, sq_abs] using h
    · rw [if_neg hx]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ mean p (fun x => (f x - mean p f) ^ 2 / t ^ 2) := mean_mono _ hpoint
    _ = _ := mean_div_const _ _ _

omit [DecidableEq Ω] in
theorem signal_term_le (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (hw : ∀ i ∈ H, 0 < w i) (i : Ω) (hi : i ∈ H) :
    (p.mass i - q.mass i) ^ 2 / w i ≤ weightedSignal p q H w := by
  unfold weightedSignal
  exact Finset.single_le_sum
    (fun j hj => div_nonneg (sq_nonneg (p.mass j - q.mass j)) (hw j hj).le) hi

omit [DecidableEq Ω] in
theorem weighted_ratio_square_bound (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (M R : ℝ) (hw : ∀ i ∈ H, 0 < w i)
    (hfloor : ∀ i ∈ H, 1 ≤ M * R * w i) (i : Ω) (hi : i ∈ H) :
    (p.mass i - q.mass i) ^ 2 / w i ^ 2 ≤ M * R * weightedSignal p q H w := by
  have hwi : 1 / w i ≤ M * R := (div_le_iff₀ (hw i hi)).2 (hfloor i hi)
  have hE := weightedSignal_nonneg p q H w (fun j hj => (hw j hj).le)
  calc
    _ = ((p.mass i - q.mass i) ^ 2 / w i) * (1 / w i) := by ring
    _ ≤ weightedSignal p q H w * (M * R) :=
      mul_le_mul (signal_term_le p q H w hw i hi) hwi (one_div_nonneg.mpr (hw i hi).le) hE
    _ = _ := by ring

omit [DecidableEq Ω] in
theorem weighted_quadratic_mass_bound (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (M R : ℝ) (hw : ∀ i ∈ H, 0 < w i)
    (hfloor : ∀ i ∈ H, 1 ≤ M * R * w i)
    (href : (∑ i ∈ H, q.mass i ^ 2 / w i ^ 2) ≤ R ^ 2) :
    varianceQuadraticTerm p H w ≤ 2 * R ^ 2 + 2 * M * R * weightedSignal p q H w := by
  have hdelta : (∑ i ∈ H, (p.mass i - q.mass i) ^ 2 / w i ^ 2) ≤ M * R * weightedSignal p q H w := by
    unfold weightedSignal
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hwi : 1 / w i ≤ M * R := (div_le_iff₀ (hw i hi)).2 (hfloor i hi)
    calc
      _ = ((p.mass i - q.mass i) ^ 2 / w i) * (1 / w i) := by ring
      _ ≤ ((p.mass i - q.mass i) ^ 2 / w i) * (M * R) :=
        mul_le_mul_of_nonneg_left hwi (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = _ := by ring
  have hsum : varianceQuadraticTerm p H w ≤
      2 * (∑ i ∈ H, q.mass i ^ 2 / w i ^ 2) +
        2 * (∑ i ∈ H, (p.mass i - q.mass i) ^ 2 / w i ^ 2) := by
    unfold varianceQuadraticTerm
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hs : p.mass i ^ 2 ≤ 2 * q.mass i ^ 2 + 2 * (p.mass i - q.mass i) ^ 2 := by
      nlinarith [sq_nonneg (p.mass i - 2 * q.mass i)]
    have h := div_le_div_of_nonneg_right hs (sq_nonneg (w i))
    convert h using 1
    ring
  linarith

omit [DecidableEq Ω] in
theorem weighted_linear_mass_bound (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (M R : ℝ) (hM : 0 < M) (hw : ∀ i ∈ H, 0 < w i)
    (hfloor : ∀ i ∈ H, 1 ≤ M * R * w i)
    (hq : ∀ i ∈ H, q.mass i ≤ R * w i)
    (hsep : 100000000 * R / M ≤ weightedSignal p q H w) :
    varianceLinearTerm p q H w ≤ R * weightedSignal p q H w +
      M * weightedSignal p q H w ^ 2 / 10000 := by
  let E := weightedSignal p q H w
  have hE : 0 ≤ E := weightedSignal_nonneg p q H w (fun i hi => (hw i hi).le)
  have hraw : 100000000 * R ≤ M * E := by
    have h := (div_le_iff₀ hM).mp hsep
    dsimp [E]
    nlinarith
  have hpoint : ∀ i ∈ H, p.mass i / w i ≤ R + M * E / 10000 := by
    intro i hi
    have hsq := weighted_ratio_square_bound p q H w M R hw hfloor i hi
    have hmul := mul_le_mul_of_nonneg_left hraw (mul_nonneg hM.le hE)
    have hsq' : (|p.mass i - q.mass i| / w i) ^ 2 ≤ (M * E / 10000) ^ 2 := by
      rw [div_pow, sq_abs]
      dsimp [E] at *
      nlinarith
    have hdelta : |p.mass i - q.mass i| / w i ≤ M * E / 10000 := by
      have h0 : 0 ≤ |p.mass i - q.mass i| / w i := div_nonneg (abs_nonneg _) (hw i hi).le
      have h1 : 0 ≤ M * E / 10000 := by positivity
      nlinarith
    have hqi : q.mass i / w i ≤ R := (div_le_iff₀ (hw i hi)).2 (hq i hi)
    have hp : p.mass i ≤ q.mass i + |p.mass i - q.mass i| := by
      have h := le_abs_self (p.mass i - q.mass i)
      linarith
    calc
      _ ≤ (q.mass i + |p.mass i - q.mass i|) / w i :=
        div_le_div_of_nonneg_right hp (hw i hi).le
      _ = q.mass i / w i + |p.mass i - q.mass i| / w i := add_div _ _ _
      _ ≤ _ := add_le_add hqi hdelta
  calc
    _ ≤ (R + M * E / 10000) * weightedSignal p q H w := by
      unfold varianceLinearTerm weightedSignal
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (p.mass i / w i) * ((p.mass i - q.mass i) ^ 2 / w i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hpoint i hi)
          (div_nonneg (sq_nonneg _) (hw i hi).le)
    _ = _ := by dsimp [E]; ring

def weightedTest (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m : ℕ) (R : ℝ) : RandomizedTest (Fin (m + m) → Ω) where
  reject sample := if 100 * R / m < fixedCrossStatistic q H w m m sample then 1 else 0
  nonneg sample := by split <;> norm_num
  le_one sample := by split <;> norm_num

theorem weightedTest_null_error (q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m : ℕ) (R : ℝ) (hm : 0 < m) (hR : 0 < R)
    (href : (∑ i ∈ H, q.mass i ^ 2 / w i ^ 2) ≤ R ^ 2) :
    expectation (productLaw q (m + m)) (weightedTest q H w m R) ≤ 1 / 10000 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ht : 0 < 100 * R / (m : ℝ) := by positivity
  have hmean := mean_fixedCrossStatistic q q H w m m hm hm
  rw [weightedSignal_null] at hmean
  have hv := variance_fixedCrossStatistic_le q q H w m m hm hm
  simp only [varianceLinearTerm, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_div, Finset.sum_const_zero, zero_add] at hv
  have htail := scalar_event_probability_le (productLaw q (m + m))
    (fixedCrossStatistic q H w m m) (100 * R / m) ht
    (fun sample => 100 * R / m < fixedCrossStatistic q H w m m sample) (by
      intro sample hs
      rw [hmean, sub_zero]
      exact hs.le.trans (le_abs_self _))
  apply htail.trans
  calc
    _ ≤ (varianceQuadraticTerm q H w / ((m : ℝ) * m)) / (100 * R / m) ^ 2 :=
      div_le_div_of_nonneg_right hv (sq_nonneg _)
    _ ≤ (R ^ 2 / ((m : ℝ) * m)) / (100 * R / m) ^ 2 :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right href (by positivity)) (sq_nonneg _)
    _ = _ := by field_simp; norm_num

theorem quadratic_relative_variance_arithmetic (M R E A B : ℝ)
    (hM : 0 < M) (hR : 0 < R) (hE : 0 < E)
    (hsep : 100000000 * R / M ≤ E)
    (hA : A ≤ R * E + M * E ^ 2 / 10000)
    (hB : B ≤ 2 * R ^ 2 + 2 * M * R * E) :
    (A / M + A / M + B / (M * M)) / (E / 2) ^ 2 ≤ 1 / 200 := by
  let r := R / (M * E)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr : r ≤ 1 / 100000000 := by
    apply (div_le_iff₀ (mul_pos hM hE)).2
    have h := (div_le_iff₀ hM).mp hsep
    nlinarith
  calc
    _ ≤ ((R * E + M * E ^ 2 / 10000) / M +
        (R * E + M * E ^ 2 / 10000) / M +
        (2 * R ^ 2 + 2 * M * R * E) / (M * M)) / (E / 2) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact add_le_add (add_le_add (div_le_div_of_nonneg_right hA hM.le)
        (div_le_div_of_nonneg_right hA hM.le))
        (div_le_div_of_nonneg_right hB (mul_nonneg hM.le hM.le))
    _ = 16 * r + 8 / 10000 + 8 * r ^ 2 := by
      dsimp [r]
      field_simp
      ring
    _ ≤ _ := by
      have hr1 : r ≤ 1 := by linarith
      have hrsq : r ^ 2 ≤ r := by nlinarith
      nlinarith

theorem weightedTest_alternative_error (p q : Probability Ω) (H : Finset Ω) (w : Ω → ℝ)
    (m : ℕ) (R : ℝ) (hm : 0 < m) (hR : 0 < R)
    (hw : ∀ i ∈ H, 0 < w i)
    (hfloor : ∀ i ∈ H, 1 ≤ (m : ℝ) * R * w i)
    (hq : ∀ i ∈ H, q.mass i ≤ R * w i)
    (href : (∑ i ∈ H, q.mass i ^ 2 / w i ^ 2) ≤ R ^ 2)
    (hsep : 100000000 * R / m ≤ weightedSignal p q H w) :
    1 - expectation (productLaw p (m + m)) (weightedTest q H w m R) ≤ 1 / 200 := by
  let E := weightedSignal p q H w
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hE : 0 < E := lt_of_lt_of_le (by positivity) hsep
  have hmean := mean_fixedCrossStatistic p q H w m m hm hm
  have hthreshold : 100 * R / (m : ℝ) ≤ E / 2 := by
    have hratio : 0 ≤ R / (m : ℝ) := by positivity
    have hs : 100000000 * (R / (m : ℝ)) ≤ E := by simpa only [mul_div_assoc] using hsep
    rw [mul_div_assoc]
    nlinarith
  have hmiss : 1 - expectation (productLaw p (m + m)) (weightedTest q H w m R) =
      mean (productLaw p (m + m)) (fun sample =>
        if fixedCrossStatistic q H w m m sample ≤ 100 * R / m then 1 else 0) := by
    have hpoint : (fun sample => 1 - (weightedTest q H w m R).reject sample) =
        (fun sample => if fixedCrossStatistic q H w m m sample ≤ 100 * R / m then (1 : ℝ) else 0) := by
      funext sample
      change 1 - (if 100 * R / (m : ℝ) < fixedCrossStatistic q H w m m sample then 1 else 0) =
        (if fixedCrossStatistic q H w m m sample ≤ 100 * R / m then 1 else 0)
      by_cases h : 100 * R / (m : ℝ) < fixedCrossStatistic q H w m m sample
      · rw [if_pos h, if_neg (not_le.mpr h)]
        norm_num
      · rw [if_neg h, if_pos (le_of_not_gt h)]
        norm_num
    rw [← hpoint, mean_sub, mean_const]
    rfl
  rw [hmiss]
  have htail := scalar_event_probability_le (productLaw p (m + m))
    (fixedCrossStatistic q H w m m) (E / 2) (half_pos hE)
    (fun sample => fixedCrossStatistic q H w m m sample ≤ 100 * R / m) (by
      intro sample hs
      rw [hmean]
      have ha := neg_le_abs (fixedCrossStatistic q H w m m sample - E)
      dsimp [E] at *
      linarith)
  apply htail.trans
  calc
    _ ≤ (varianceLinearTerm p q H w / m + varianceLinearTerm p q H w / m +
        varianceQuadraticTerm p H w / ((m : ℝ) * m)) / (E / 2) ^ 2 :=
      div_le_div_of_nonneg_right (variance_fixedCrossStatistic_le p q H w m m hm hm) (sq_nonneg _)
    _ ≤ _ := quadratic_relative_variance_arithmetic (m : ℝ) R E _ _ hmR hR hE hsep
      (weighted_linear_mass_bound p q H w (m : ℝ) R hmR hw hfloor hq hsep)
      (weighted_quadratic_mass_bound p q H w (m : ℝ) R hw hfloor href)

end IdentityTesting.ProfileTesting
