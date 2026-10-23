import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

/-!
# Finite observation spaces and the finite-prior testing obstruction

The objects here are actual normalized probability vectors.  In particular,
neither the testing bound nor the normalization of a mixture is an input field.
The observation space may subsequently be instantiated by a finite sample space.
This module does not assert the manuscript's main sample-complexity theorem.
-/

namespace IdentityTesting.FiniteTesting

open scoped BigOperators

universe u v

/-- A probability law on an arbitrary finite observation space. -/
structure Probability (Ω : Type u) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

/-- A randomized test, represented by its conditional rejection probability. -/
structure RandomizedTest (Ω : Type u) where
  reject : Ω → ℝ
  nonneg : ∀ x, 0 ≤ reject x
  le_one : ∀ x, reject x ≤ 1

variable {Ω : Type u} [Fintype Ω]

/-- The rejection probability of a test under a finite law. -/
def expectation (p : Probability Ω) (test : RandomizedTest Ω) : ℝ :=
  ∑ x, p.mass x * test.reject x

/-- Total variation with the standard one-half normalization. -/
def totalVariation (p q : Probability Ω) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p.mass x - q.mass x|

theorem totalVariation_symm (p q : Probability Ω) :
    totalVariation p q = totalVariation q p := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

theorem expectation_nonneg (p : Probability Ω) (test : RandomizedTest Ω) :
    0 ≤ expectation p test := by
  exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (test.nonneg x)

theorem expectation_le_one (p : Probability Ω) (test : RandomizedTest Ω) :
    expectation p test ≤ 1 := by
  calc
    expectation p test ≤ ∑ x, p.mass x * 1 := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (test.le_one x) (p.nonneg x)
    _ = 1 := by simpa only [mul_one] using p.total

private theorem test_mul_bound (d t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    d * t ≤ (|d| + d) / 2 := by
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd]
    have h := mul_le_mul_of_nonneg_left ht1 hd
    linarith
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [abs_of_nonpos hd']
    have h := mul_nonpos_of_nonpos_of_nonneg hd' ht0
    linarith

/-- A test with values in `[0,1]` separates two normalized laws by at most TV. -/
theorem expectation_sub_le_totalVariation (p q : Probability Ω)
    (test : RandomizedTest Ω) :
    expectation p test - expectation q test ≤ totalVariation p q := by
  calc
    expectation p test - expectation q test =
        ∑ x, (p.mass x - q.mass x) * test.reject x := by
      simp only [expectation, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ x, (|p.mass x - q.mass x| + (p.mass x - q.mass x)) / 2 := by
      apply Finset.sum_le_sum
      intro x _
      exact test_mul_bound _ _ (test.nonneg x) (test.le_one x)
    _ = totalVariation p q := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, p.total, q.total, sub_self, add_zero,
        totalVariation]
      ring

theorem abs_expectation_sub_le_totalVariation (p q : Probability Ω)
    (test : RandomizedTest Ω) :
    |expectation p test - expectation q test| ≤ totalVariation p q := by
  apply abs_le.mpr
  constructor
  · have h := expectation_sub_le_totalVariation q p test
    rw [totalVariation_symm q p] at h
    linarith
  · exact expectation_sub_le_totalVariation p q test

/-- The categorical IID sample law on tuples `Fin n → Ω`, including `n = 0`. -/
def productLaw (p : Probability Ω) (n : ℕ) : Probability (Fin n → Ω) where
  mass sample := ∏ j, p.mass (sample j)
  nonneg sample := Finset.prod_nonneg fun j _ => p.nonneg (sample j)
  total := by
    calc
      (∑ sample : Fin n → Ω, ∏ j, p.mass (sample j)) = (∑ x, p.mass x) ^ n :=
        (Fintype.sum_pow p.mass n).symm
      _ = 1 := by rw [p.total, one_pow]

@[simp] theorem productLaw_mass (p : Probability Ω) (n : ℕ) (sample : Fin n → Ω) :
    (productLaw p n).mass sample = ∏ j, p.mass (sample j) := rfl

variable {I : Type v} [Fintype I]

/-- The actual convex mixture of a finite family of probability laws. -/
def mixture (weights : Probability I) (laws : I → Probability Ω) : Probability Ω where
  mass x := ∑ i, weights.mass i * (laws i).mass x
  nonneg x := Finset.sum_nonneg fun i _ =>
    mul_nonneg (weights.nonneg i) ((laws i).nonneg x)
  total := by
    calc
      (∑ x, ∑ i, weights.mass i * (laws i).mass x) =
          ∑ i, ∑ x, weights.mass i * (laws i).mass x := Finset.sum_comm
      _ = ∑ i, weights.mass i * (∑ x, (laws i).mass x) := by
        simp only [Finset.mul_sum]
      _ = 1 := by simp only [Probability.total, mul_one]

@[simp] theorem mixture_mass (weights : Probability I) (laws : I → Probability Ω) (x : Ω) :
    (mixture weights laws).mass x = ∑ i, weights.mass i * (laws i).mass x := rfl

/-- Testing a mixture is exactly averaging the rejection probabilities. -/
theorem expectation_mixture (weights : Probability I)
    (laws : I → Probability Ω) (test : RandomizedTest Ω) :
    expectation (mixture weights laws) test =
      ∑ i, weights.mass i * expectation (laws i) test := by
  calc
    expectation (mixture weights laws) test =
        ∑ x, ∑ i, weights.mass i * ((laws i).mass x * test.reject x) := by
      simp only [expectation, mixture, Finset.sum_mul, mul_assoc]
    _ = ∑ i, ∑ x, weights.mass i * ((laws i).mass x * test.reject x) :=
      Finset.sum_comm
    _ = ∑ i, weights.mass i * expectation (laws i) test := by
      simp only [expectation, Finset.mul_sum]

theorem average_alternative_error_eq (weights : Probability I)
    (laws : I → Probability Ω) (test : RandomizedTest Ω) :
    (∑ i, weights.mass i * (1 - expectation (laws i) test)) =
      1 - expectation (mixture weights laws) test := by
  rw [expectation_mixture]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, weights.total]

/-- Null error plus prior-averaged alternative error is at least `1 - TV`. -/
theorem null_error_add_average_alternative_error_lower_bound
    (weights : Probability I) (laws : I → Probability Ω)
    (null : Probability Ω) (test : RandomizedTest Ω) :
    1 - totalVariation (mixture weights laws) null ≤
      expectation null test +
        ∑ i, weights.mass i * (1 - expectation (laws i) test) := by
  rw [average_alternative_error_eq]
  have h := expectation_sub_le_totalVariation (mixture weights laws) null test
  linarith

/-- The prior obstruction only needs power on alternatives of positive weight. -/
theorem finite_prior_obstruction_on_support (weights : Probability I)
    (laws : I → Probability Ω) (null : Probability Ω)
    (hTV : totalVariation (mixture weights laws) null < (1 : ℝ) / 3) :
    ¬ ∃ test : RandomizedTest Ω,
      expectation null test ≤ (1 : ℝ) / 3 ∧
      ∀ i, 0 < weights.mass i → (2 : ℝ) / 3 ≤ expectation (laws i) test := by
  rintro ⟨test, hnull, halt⟩
  have havg : (2 : ℝ) / 3 ≤ expectation (mixture weights laws) test := by
    rw [expectation_mixture]
    calc
      (2 : ℝ) / 3 = ∑ i, weights.mass i * ((2 : ℝ) / 3) := by
        rw [← Finset.sum_mul, weights.total, one_mul]
      _ ≤ ∑ i, weights.mass i * expectation (laws i) test := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hpos : 0 < weights.mass i
        · exact mul_le_mul_of_nonneg_left (halt i hpos) (weights.nonneg i)
        · have hzero : weights.mass i = 0 :=
            le_antisymm (le_of_not_gt hpos) (weights.nonneg i)
          simp only [hzero, zero_mul, le_refl]
  have hdiff := expectation_sub_le_totalVariation (mixture weights laws) null test
  linarith

/-- If the finite-prior mixture is within `1/3` of the null, no test can
reject the null at most `1/3` and every alternative at least `2/3`.
The laws are observation laws; sample-product constructions are separate. -/
theorem finite_prior_obstruction (weights : Probability I)
    (laws : I → Probability Ω) (null : Probability Ω)
    (hTV : totalVariation (mixture weights laws) null < (1 : ℝ) / 3) :
    ¬ ∃ test : RandomizedTest Ω,
      expectation null test ≤ (1 : ℝ) / 3 ∧
      ∀ i, (2 : ℝ) / 3 ≤ expectation (laws i) test := by
  rintro ⟨test, hnull, halt⟩
  apply finite_prior_obstruction_on_support weights laws null hTV
  exact ⟨test, hnull, fun i _ => halt i⟩

/-- The equivalent formulation in terms of null and alternative errors. -/
theorem finite_prior_errors_obstruction (weights : Probability I)
    (laws : I → Probability Ω) (null : Probability Ω)
    (hTV : totalVariation (mixture weights laws) null < (1 : ℝ) / 3) :
    ¬ ∃ test : RandomizedTest Ω,
      expectation null test ≤ (1 : ℝ) / 3 ∧
      ∀ i, 1 - expectation (laws i) test ≤ (1 : ℝ) / 3 := by
  rintro ⟨test, hnull, halt⟩
  apply finite_prior_obstruction weights laws null hTV
  refine ⟨test, hnull, ?_⟩
  intro i
  have h := halt i
  linarith

/-- The finite-prior obstruction instantiated by actual categorical IID laws.
The separation hypothesis concerns the original one-observation laws. -/
theorem finite_iid_prior_obstruction (weights : Probability I)
    (alternatives : I → Probability Ω) (null : Probability Ω)
    (ε : ℝ) (n : ℕ)
    (hseparated : ∀ i, ε < totalVariation (alternatives i) null)
    (hTV : totalVariation
      (mixture weights (fun i => productLaw (alternatives i) n))
      (productLaw null n) < (1 : ℝ) / 3) :
    ¬ ∃ test : RandomizedTest (Fin n → Ω),
      expectation (productLaw null n) test ≤ (1 : ℝ) / 3 ∧
      ∀ p : Probability Ω, ε < totalVariation p null →
        (2 : ℝ) / 3 ≤ expectation (productLaw p n) test := by
  rintro ⟨test, hnull, halt⟩
  apply finite_prior_obstruction weights
    (fun i => productLaw (alternatives i) n) (productLaw null n) hTV
  exact ⟨test, hnull, fun i => halt (alternatives i) (hseparated i)⟩

/-- The IID formulation with separation required precisely on the prior support. -/
theorem finite_iid_prior_obstruction_on_support (weights : Probability I)
    (alternatives : I → Probability Ω) (null : Probability Ω)
    (ε : ℝ) (n : ℕ)
    (hseparated : ∀ i, 0 < weights.mass i → ε < totalVariation (alternatives i) null)
    (hTV : totalVariation
      (mixture weights (fun i => productLaw (alternatives i) n))
      (productLaw null n) < (1 : ℝ) / 3) :
    ¬ ∃ test : RandomizedTest (Fin n → Ω),
      expectation (productLaw null n) test ≤ (1 : ℝ) / 3 ∧
      ∀ p : Probability Ω, ε < totalVariation p null →
        (2 : ℝ) / 3 ≤ expectation (productLaw p n) test := by
  rintro ⟨test, hnull, halt⟩
  apply finite_prior_obstruction_on_support weights
    (fun i => productLaw (alternatives i) n) (productLaw null n) hTV
  exact ⟨test, hnull, fun i hi => halt (alternatives i) (hseparated i hi)⟩

end IdentityTesting.FiniteTesting
