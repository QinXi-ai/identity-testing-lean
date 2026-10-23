import IdentityTesting.EventCounts
import Mathlib.Analysis.Complex.Exponential

/-! One-sided event-count testing via explicit finite IID exponential moments. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.EventCounts
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def eventCount (E : Finset Ω) (n : ℕ) (sample : Fin n → Ω) : ℝ :=
  ∑ j, eventIndicator E (sample j)

omit [Fintype Ω] in
theorem eventCount_eq_mul_frequency (E : Finset Ω) (n : ℕ) (hn : 0 < n)
    (sample : Fin n → Ω) : eventCount E n sample = (n : ℝ) * eventFrequency E n sample := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold eventCount eventFrequency
  field_simp

theorem mean_exp_eventIndicator (p : Probability Ω) (E : Finset Ω) (t : ℝ) :
    mean p (fun x => Real.exp (t * eventIndicator E x)) =
      1 + eventMass p E * (Real.exp t - 1) := by
  have hfun : (fun x => Real.exp (t * eventIndicator E x)) =
      (fun x => 1 + eventIndicator E x * (Real.exp t - 1)) := by
    funext x
    unfold eventIndicator
    split_ifs <;> simp
  rw [hfun, mean_add, mean_const, mean_mul_const, mean_eventIndicator]

theorem mean_exp_eventCount (p : Probability Ω) (E : Finset Ω) (n : ℕ) (t : ℝ) :
    mean (productLaw p n) (fun sample => Real.exp (t * eventCount E n sample)) =
      (1 + eventMass p E * (Real.exp t - 1)) ^ n := by
  have hfun : (fun sample : Fin n → Ω => Real.exp (t * eventCount E n sample)) =
      (fun sample => ∏ j, Real.exp (t * eventIndicator E (sample j))) := by
    funext sample
    simp [eventCount, Finset.mul_sum, Real.exp_sum]
  rw [hfun, mean_productLaw_product p n (fun _ x => Real.exp (t * eventIndicator E x))]
  change (∏ j : Fin n, mean p (fun x => Real.exp (t * eventIndicator E x))) = _
  simp [mean_exp_eventIndicator]

theorem mean_exp_eventCount_le (p : Probability Ω) (E : Finset Ω) (n : ℕ) (t : ℝ) :
    mean (productLaw p n) (fun sample => Real.exp (t * eventCount E n sample)) ≤
      Real.exp ((n : ℝ) * eventMass p E * (Real.exp t - 1)) := by
  rw [mean_exp_eventCount]
  have hbase : 0 ≤ 1 + eventMass p E * (Real.exp t - 1) := by
    rw [← mean_exp_eventIndicator]
    exact mean_nonneg _ (fun x => (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (eventMass p E * (Real.exp t - 1)) ^ n :=
      pow_le_pow_left₀ hbase (by simpa [add_comm] using Real.add_one_le_exp (eventMass p E * (Real.exp t - 1))) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem exponential_event_probability_le (p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (t k : ℝ) (B : (Fin n → Ω) → Prop) [DecidablePred B]
    (hB : ∀ sample, B sample → t * k ≤ t * eventCount E n sample) :
    mean (productLaw p n) (fun sample => if B sample then 1 else 0) ≤
      Real.exp ((n : ℝ) * eventMass p E * (Real.exp t - 1) - t * k) := by
  classical
  have hpoint : ∀ sample, (if B sample then (1 : ℝ) else 0) ≤
      Real.exp (t * eventCount E n sample) / Real.exp (t * k) := by
    intro sample
    by_cases hs : B sample
    · simp only [if_pos hs]
      apply (le_div_iff₀ (Real.exp_pos _)).2
      simpa using Real.exp_le_exp.mpr (hB sample hs)
    · simp only [if_neg hs]
      positivity
  calc
    _ ≤ mean (productLaw p n) (fun sample => Real.exp (t * eventCount E n sample) / Real.exp (t * k)) :=
      mean_mono _ hpoint
    _ = mean (productLaw p n) (fun sample => Real.exp (t * eventCount E n sample)) / Real.exp (t * k) :=
      mean_div_const _ _ _
    _ ≤ Real.exp ((n : ℝ) * eventMass p E * (Real.exp t - 1)) / Real.exp (t * k) :=
      div_le_div_of_nonneg_right (mean_exp_eventCount_le p E n t) (Real.exp_pos _).le
    _ = _ := (Real.exp_sub _ _).symm

theorem exp_neg_quarter_le : Real.exp (-(1 : ℝ) / 4) ≤ 25 / 32 := by
  have h := Real.exp_bound (x := -(1 : ℝ) / 4) (n := 4) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hh := (abs_le.mp h).2
  linarith

theorem exp_half_le : Real.exp ((1 : ℝ) / 2) ≤ 33 / 20 := by
  have h := Real.exp_bound' (x := (1 : ℝ) / 2) (n := 4) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

def lowerCountTest (E : Finset Ω) (n : ℕ) (v : ℝ) : RandomizedTest (Fin n → Ω) where
  reject sample := if eventFrequency E n sample < 3 * v / 4 then 1 else 0
  nonneg sample := by split <;> norm_num
  le_one sample := by split <;> norm_num

theorem lowerCountTest_null_error (q : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) :
    expectation (productLaw q n) (lowerCountTest E n (eventMass q E)) ≤
      Real.exp (-(n : ℝ) * eventMass q E / 32) := by
  let v := eventMass q E
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hv : 0 ≤ v := eventMass_nonneg q E
  have h := exponential_event_probability_le q E n (-(1 : ℝ) / 4) (3 * (n : ℝ) * v / 4)
    (fun sample => eventFrequency E n sample < 3 * v / 4) (by
      intro sample hs
      rw [eventCount_eq_mul_frequency E n hn]
      have hm := mul_le_mul_of_nonneg_left hs.le hnR.le
      nlinarith)
  apply h.trans
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_left exp_neg_quarter_le (mul_nonneg hnR.le hv)
  dsimp [v] at *
  nlinarith

theorem lowerCountTest_alternative_error (q p : Probability Ω) (E : Finset Ω)
    (n : ℕ) (hn : 0 < n) (hsep : eventMass p E ≤ eventMass q E / 2) :
    1 - expectation (productLaw p n) (lowerCountTest E n (eventMass q E)) ≤
      Real.exp (-(n : ℝ) * eventMass q E / 20) := by
  let v := eventMass q E
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hv : 0 ≤ v := eventMass_nonneg q E
  have hmiss : 1 - expectation (productLaw p n) (lowerCountTest E n v) =
      mean (productLaw p n) (fun sample => if 3 * v / 4 ≤ eventFrequency E n sample then 1 else 0) := by
    have hpoint : (fun sample => 1 - (lowerCountTest E n v).reject sample) =
        (fun sample => if 3 * v / 4 ≤ eventFrequency E n sample then (1 : ℝ) else 0) := by
      funext sample
      change 1 - (if eventFrequency E n sample < 3 * v / 4 then 1 else 0) =
        (if 3 * v / 4 ≤ eventFrequency E n sample then 1 else 0)
      by_cases h : eventFrequency E n sample < 3 * v / 4
      · rw [if_pos h, if_neg (not_le.mpr h)]
        norm_num
      · rw [if_neg h, if_pos (le_of_not_gt h)]
        norm_num
    rw [← hpoint, mean_sub, mean_const]
    rfl
  have h := exponential_event_probability_le p E n ((1 : ℝ) / 2) (3 * (n : ℝ) * v / 4)
    (fun sample => 3 * v / 4 ≤ eventFrequency E n sample) (by
      intro sample hs
      rw [eventCount_eq_mul_frequency E n hn]
      have hm := mul_le_mul_of_nonneg_left hs hnR.le
      nlinarith)
  have hcoeff : eventMass p E * (Real.exp ((1 : ℝ) / 2) - 1) ≤ v * (13 / 40) := by
    have he0 : 0 ≤ Real.exp ((1 : ℝ) / 2) - 1 := by
      have := Real.add_one_le_exp ((1 : ℝ) / 2)
      linarith
    calc
      _ ≤ (v / 2) * (Real.exp ((1 : ℝ) / 2) - 1) := mul_le_mul_of_nonneg_right hsep he0
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left exp_half_le hv]
  rw [hmiss]
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hc := mul_le_mul_of_nonneg_left hcoeff hnR.le
  dsimp [v] at *
  nlinarith

end IdentityTesting.EventCounts
