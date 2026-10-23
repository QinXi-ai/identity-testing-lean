import IdentityTesting.CountableBatchProduct
import IdentityTesting.EventChernoff

/-! The exact 100-batch Hoeffding bound used in the manuscript.
For error probability at most 3/8, a fixed exponential tilt proves
exp(-2 * 100 * (1/8)^2). Internal coins and batch independence are constructed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting
open FiniteTesting FiniteIID EventCounts

private theorem exp_seven_thirtytwo_ge : (199 : ℝ) / 160 ≤ Real.exp (7 / 32 : ℝ) := by
  have h := Real.exp_bound (x := (7 : ℝ) / 32) (n := 4) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith [(abs_le.mp h).1]

/-- A fixed-parameter Hoeffding inequality, proved from the actual IID MGF. -/
theorem hundred_batch_event_error (p : Probability Bool) (E : Finset Bool)
    (hp : eventMass p E ≤ 3 / 8)
    (B : (Fin 100 → Bool) → Prop) [DecidablePred B]
    (hB : ∀ b, B b → (50 : ℝ) ≤ eventCount E 100 b) :
    mean (productLaw p 100) (fun b => if B b then 1 else 0) ≤
      Real.exp (-2 * 100 * (1 / 8 : ℝ) ^ 2) := by
  have hpoint : ∀ b : Fin 100 → Bool, (if B b then (1 : ℝ) else 0) ≤
      Real.exp ((1 / 2 : ℝ) * eventCount E 100 b) / Real.exp 25 := by
    intro b
    by_cases hb : B b
    · rw [if_pos hb]
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa using Real.exp_le_exp.mpr (by linarith [hB b hb])
    · rw [if_neg hb]
      positivity
  have hbase0 : 0 ≤ 1 + eventMass p E * (Real.exp ((1 : ℝ) / 2) - 1) := by
    rw [← mean_exp_eventIndicator]
    exact mean_nonneg _ (fun _ => (Real.exp_pos _).le)
  have hbase : 1 + eventMass p E * (Real.exp ((1 : ℝ) / 2) - 1) ≤
      Real.exp ((7 : ℝ) / 32) := by
    have hexp0 : 0 ≤ Real.exp ((1 : ℝ) / 2) - 1 := by
      linarith [Real.add_one_le_exp ((1 : ℝ) / 2)]
    have h := mul_le_mul_of_nonneg_right hp hexp0
    have he := exp_half_le
    have hlo := exp_seven_thirtytwo_ge
    nlinarith
  calc
    _ ≤ mean (productLaw p 100) (fun b =>
        Real.exp ((1 / 2 : ℝ) * eventCount E 100 b) / Real.exp 25) := mean_mono _ hpoint
    _ = (1 + eventMass p E * (Real.exp ((1 : ℝ) / 2) - 1)) ^ 100 / Real.exp 25 := by
      rw [mean_div_const, mean_exp_eventCount]
    _ ≤ Real.exp ((7 : ℝ) / 32) ^ 100 / Real.exp 25 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hbase0 hbase 100) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_sub]; norm_num

theorem hundred_batch_exp_lt_third : Real.exp (-2 * 100 * (1 / 8 : ℝ) ^ 2) < 1 / 3 := by
  rw [show -2 * 100 * (1 / 8 : ℝ) ^ 2 = -((25 : ℝ) / 8) by norm_num, Real.exp_neg]
  rw [← one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  nlinarith [Real.add_one_le_exp ((25 : ℝ) / 8)]

def majorityBits : FiniteTesting.RandomizedTest (Fin 100 → Bool) where
  reject b := if (50 : ℝ) ≤ eventCount {true} 100 b then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  le_one b := by split_ifs <;> norm_num

def hundredBatchTest {n : ℕ} (test : IdentityTesting.RandomizedTest n) :
    IdentityTesting.RandomizedTest (100 * n) where
  reject x := expectation (conditionalBits test 100 x) majorityBits
  nonneg x := expectation_nonneg _ _
  le_one x := expectation_le_one _ _

set_option maxRecDepth 4096 in
theorem hundredBatchTest_rejection (p : DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) :
    rejectionProbability p (hundredBatchTest test) =
      expectation (productLaw (testBitLaw p test) 100) majorityBits :=
  conditional_bits_expectation p test 100 majorityBits.reject

theorem testBitLaw_event_true (p : DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) :
    eventMass (testBitLaw p test) {true} = rejectionProbability p test := by
  simp [eventMass, testBitLaw, coinLaw, coinMass]

theorem testBitLaw_event_false (p : DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) :
    eventMass (testBitLaw p test) {false} = acceptanceProbability p test := by
  have h := rejection_add_acceptance p test
  simp [eventMass, testBitLaw, coinLaw, coinMass]
  linarith

theorem bool_event_counts_sum (b : Fin 100 → Bool) :
    eventCount {true} 100 b + eventCount {false} 100 b = 100 := by
  unfold eventCount
  rw [← Finset.sum_add_distrib]
  have he : ∀ j, eventIndicator {true} (b j) + eventIndicator {false} (b j) = 1 := by
    intro j
    cases b j <;> simp [eventIndicator]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  norm_num

theorem hundredBatchTest_null_error (p : DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) (hp : rejectionProbability p test ≤ 3 / 8) :
    rejectionProbability p (hundredBatchTest test) ≤ Real.exp (-2 * 100 * (1 / 8 : ℝ) ^ 2) := by
  rw [hundredBatchTest_rejection]
  exact hundred_batch_event_error (testBitLaw p test) {true}
    (by rwa [testBitLaw_event_true]) _ (fun _ h => h)

theorem hundredBatchTest_alternative_error (p : DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) (hp : acceptanceProbability p test ≤ 3 / 8) :
    acceptanceProbability p (hundredBatchTest test) ≤ Real.exp (-2 * 100 * (1 / 8 : ℝ) ^ 2) := by
  have h := rejection_add_acceptance p (hundredBatchTest test)
  rw [hundredBatchTest_rejection] at h
  have he : acceptanceProbability p (hundredBatchTest test) =
      mean (productLaw (testBitLaw p test) 100)
        (fun b => if eventCount {true} 100 b < 50 then 1 else 0) := by
    have hfun : (fun b : Fin 100 → Bool => if eventCount {true} 100 b < 50 then (1 : ℝ) else 0) =
        (fun b => 1 - majorityBits.reject b) := by
      funext b
      simp only [majorityBits]
      split_ifs <;> linarith
    rw [hfun, mean_sub, mean_const]
    change _ = 1 - expectation _ majorityBits
    linarith
  rw [he]
  apply hundred_batch_event_error (testBitLaw p test) {false}
    (by rwa [testBitLaw_event_false])
  intro b hb
  linarith [bool_event_counts_sum b]

end IdentityTesting
