import IdentityTesting.ProfileTestingBounds
import IdentityTesting.ProfileTestingSeparation
import IdentityTesting.FiniteCoupling

/-! Direct full-prefix identity testing on actual fixed-size finite IID samples.
No external identity-testing theorem is assumed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u v
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def testMaximum (s t : RandomizedTest Ω) : RandomizedTest Ω where
  reject x := max (s.reject x) (t.reject x)
  nonneg x := (s.nonneg x).trans (le_max_left _ _)
  le_one x := max_le (s.le_one x) (t.le_one x)

omit [DecidableEq Ω] in
theorem expectation_testMaximum_le (p : Probability Ω) (s t : RandomizedTest Ω) :
    expectation p (testMaximum s t) ≤ expectation p s + expectation p t := by
  have h := mean_mono p (f := (testMaximum s t).reject) (g := fun x => s.reject x + t.reject x)
    (fun x => max_le (le_add_of_nonneg_right (t.nonneg x)) (le_add_of_nonneg_left (s.nonneg x)))
  simpa only [mean_add] using h

omit [DecidableEq Ω] in
theorem expectation_le_testMaximum_left (p : Probability Ω) (s t : RandomizedTest Ω) :
    expectation p s ≤ expectation p (testMaximum s t) :=
  mean_mono p (fun x => le_max_left (s.reject x) (t.reject x))

omit [DecidableEq Ω] in
theorem expectation_le_testMaximum_right (p : Probability Ω) (s t : RandomizedTest Ω) :
    expectation p t ≤ expectation p (testMaximum s t) :=
  mean_mono p (fun x => le_max_right (s.reject x) (t.reject x))

def firstBlockTest (m n : ℕ) (test : RandomizedTest (Fin m → Ω)) :
    RandomizedTest (Fin (m + n) → Ω) where
  reject sample := test.reject (firstBlock m n sample)
  nonneg _ := test.nonneg _
  le_one _ := test.le_one _

omit [DecidableEq Ω] in
theorem expectation_firstBlockTest (p : Probability Ω) (m n : ℕ)
    (test : RandomizedTest (Fin m → Ω)) :
    expectation (productLaw p (m + n)) (firstBlockTest m n test) = expectation (productLaw p m) test :=
  mean_productLaw_firstBlock p m n test.reject

def batchProfileTest (q : Probability Ω) (a : Ω) (m : ℕ) : RandomizedTest (Fin (m + m) → Ω) :=
  if 0 < weightSum q a then
    testMaximum
      (firstBlockTest m m (countTest (lightLabels q a m) m (eventMass q (lightLabels q a m)) 1000))
      (weightedTest q (heavyLabels q a m) (powerWeight q) m (Real.sqrt (weightSum q a)))
  else
    firstBlockTest m m (countTest (tailLabels a) m (eventMass q (tailLabels a)) 1000)

theorem batchProfileTest_null_error (q : Probability Ω) (a : Ω) (m : ℕ) (hm : 0 < m) :
    expectation (productLaw q (m + m)) (batchProfileTest q a m) ≤ 1 / 100 := by
  by_cases hS : 0 < weightSum q a
  · rw [batchProfileTest, if_pos hS]
    have hmax := expectation_testMaximum_le (productLaw q (m + m))
      (firstBlockTest m m (countTest (lightLabels q a m) m (eventMass q (lightLabels q a m)) 1000))
      (weightedTest q (heavyLabels q a m) (powerWeight q) m (Real.sqrt (weightSum q a)))
    rw [expectation_firstBlockTest] at hmax
    have hc := countTest_null_error q (lightLabels q a m) m 1000 hm (by norm_num)
    have href : (∑ i ∈ heavyLabels q a m, q.mass i ^ 2 / powerWeight q i ^ 2) ≤
        Real.sqrt (weightSum q a) ^ 2 := by
      rw [Real.sq_sqrt (weightSum_nonneg q a)]
      exact heavy_reference_square_sum q a m hm hS
    have hw := weightedTest_null_error q (heavyLabels q a m) (powerWeight q) m
      (Real.sqrt (weightSum q a)) hm (Real.sqrt_pos.mpr hS) href
    norm_num at hc hw ⊢
    linarith
  · rw [batchProfileTest, if_neg hS, expectation_firstBlockTest]
    have hc := countTest_null_error q (tailLabels a) m 1000 hm (by norm_num)
    norm_num at hc ⊢
    linarith

theorem batchProfileTest_alternative_error (p q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hTV : 20000 * profileRadius q a m < totalVariation p q) :
    1 - expectation (productLaw p (m + m)) (batchProfileTest q a m) ≤ 1 / 100 := by
  by_cases hS : 0 < weightSum q a
  · rw [batchProfileTest, if_pos hS]
    by_cases hcsep : 2 * countThreshold m (eventMass q (lightLabels q a m)) 1000 ≤
        |eventMass p (lightLabels q a m) - eventMass q (lightLabels q a m)|
    · have hdom := expectation_le_testMaximum_left (productLaw p (m + m))
        (firstBlockTest m m (countTest (lightLabels q a m) m (eventMass q (lightLabels q a m)) 1000))
        (weightedTest q (heavyLabels q a m) (powerWeight q) m (Real.sqrt (weightSum q a)))
      rw [expectation_firstBlockTest] at hdom
      have hc := countTest_alternative_error q p (lightLabels q a m) m 1000 hm (by norm_num) hcsep
      norm_num at hc ⊢
      linarith
    · have hsignal := heavy_signal_of_TV p q a m hm hS hTV (lt_of_not_ge hcsep)
      have href : (∑ i ∈ heavyLabels q a m, q.mass i ^ 2 / powerWeight q i ^ 2) ≤
          Real.sqrt (weightSum q a) ^ 2 := by
        rw [Real.sq_sqrt (weightSum_nonneg q a)]
        exact heavy_reference_square_sum q a m hm hS
      have hw := weightedTest_alternative_error p q (heavyLabels q a m) (powerWeight q) m
        (Real.sqrt (weightSum q a)) hm (Real.sqrt_pos.mpr hS)
        (heavy_weight_pos q a m hm hS) (heavy_weight_floor q a m hm hS)
        (fun i hi => powerWeight_reference_bound q a i (heavyLabels_subset q a m hi)) href hsignal
      have hdom := expectation_le_testMaximum_right (productLaw p (m + m))
        (firstBlockTest m m (countTest (lightLabels q a m) m (eventMass q (lightLabels q a m)) 1000))
        (weightedTest q (heavyLabels q a m) (powerWeight q) m (Real.sqrt (weightSum q a)))
      linarith
  · rw [batchProfileTest, if_neg hS, expectation_firstBlockTest]
    have hS0 : weightSum q a = 0 := le_antisymm (le_of_not_gt hS) (weightSum_nonneg q a)
    have hq0 := zero_weightSum_tail_mass q a hS0
    have ht := totalVariation_le_tail_discrepancy p q a
    have hd := discrepancy_le_mass_add p q (tailLabels a)
    rw [hq0, add_zero] at hd
    have hrad : profileRadius q a m = 1 / (m : ℝ) := by simp [profileRadius, hS0]
    rw [hrad] at hTV
    have hcsep : 2 * countThreshold m (eventMass q (tailLabels a)) 1000 ≤
        |eventMass p (tailLabels a) - eventMass q (tailLabels a)| := by
      rw [hq0, sub_zero, abs_of_nonneg (eventMass_nonneg p (tailLabels a))]
      simp only [countThreshold, zero_div, Real.sqrt_zero, zero_add]
      have hN : 0 ≤ 1 / (m : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg m)
      nlinarith
    have hc := countTest_alternative_error q p (tailLabels a) m 1000 hm (by norm_num) hcsep
    norm_num at hc ⊢
    linarith

theorem profileRadius_batch_compare (q : Probability Ω) (a : Ω) (m N : ℕ)
    (hm : 0 < m) (hN : 0 < N) (hNm : N ≤ 3 * m) :
    profileRadius q a m ≤ 3 * profileRadius q a N := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNmR : (N : ℝ) ≤ 3 * m := by exact_mod_cast hNm
  have hinv : 1 / (m : ℝ) ≤ 3 / (N : ℝ) := (div_le_div_iff₀ hmR hNR).2 (by nlinarith)
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNR
  have hs : Real.sqrt (N : ℝ) ≤ 3 * Real.sqrt (m : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hmR.le]
  have hsinv : 1 / Real.sqrt (m : ℝ) ≤ 3 / Real.sqrt (N : ℝ) :=
    (div_le_div_iff₀ hsm hsN).2 (by nlinarith)
  have hterm := mul_le_mul_of_nonneg_left hsinv
    (Real.rpow_nonneg (weightSum_nonneg q a) ((3 : ℝ) / 4))
  unfold profileRadius
  simp only [div_eq_mul_inv] at hinv hterm ⊢
  nlinarith

omit [DecidableEq Ω] in
theorem pad_test (m N : ℕ) (h : m ≤ N) (test : RandomizedTest (Fin m → Ω)) :
    ∃ padded : RandomizedTest (Fin N → Ω), ∀ p : Probability Ω,
      expectation (productLaw p N) padded = expectation (productLaw p m) test := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨firstBlockTest m k test, fun p => expectation_firstBlockTest p m k test⟩

/-- A direct full-prefix bound with an explicit universal constant. It holds for
every designated atom, hence in particular for the manuscript's mass-at-least-half atom. -/
theorem fullPrefix_identity_test (q : Probability Ω) (a : Ω) (N : ℕ) (hN : 1 ≤ N) :
    ∃ test : RandomizedTest (Fin N → Ω),
      expectation (productLaw q N) test ≤ 1 / 100 ∧
      ∀ p : Probability Ω, 60000 * profileRadius q a N < totalVariation p q →
        1 - expectation (productLaw p N) test ≤ 1 / 100 := by
  by_cases hN2 : 2 ≤ N
  · let m := N / 2
    have hm : 0 < m := by dsimp [m]; omega
    have hbudget : m + m ≤ N := by dsimp [m]; omega
    have hNm : N ≤ 3 * m := by dsimp [m]; omega
    obtain ⟨test, htest⟩ := pad_test (m + m) N hbudget (batchProfileTest q a m)
    refine ⟨test, ?_, ?_⟩
    · rw [htest q]
      exact batchProfileTest_null_error q a m hm
    · intro p hp
      rw [htest p]
      apply batchProfileTest_alternative_error p q a m hm
      have hrad := profileRadius_batch_compare q a m N hm (by omega) hNm
      linarith
  · have hN1 : N = 1 := by omega
    let accept : RandomizedTest (Fin N → Ω) :=
      { reject := fun _ => 0, nonneg := fun _ => le_rfl, le_one := fun _ => by norm_num }
    refine ⟨accept, ?_, ?_⟩
    · simp [expectation, accept]
    · intro p hp
      have hrad := profileRadius_floor q a N
      rw [hN1] at hrad
      norm_num at hrad
      rw [hN1] at hp
      have htv := FiniteTesting.totalVariation_le_one p q
      exfalso
      linarith

end IdentityTesting.ProfileTesting
