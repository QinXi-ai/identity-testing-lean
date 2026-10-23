import IdentityTesting.Endpoints
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp

/-!
# The point-mass branch in the original countable testing model

All observations and alternatives remain on `ℕ`.  For `0 < ε < 1`, an
explicit randomized test succeeds at `ceil (1 / ε)` samples, while every
successful test uses at least `(1 / ε) / 4` samples.  The lower bound uses
a genuine two-point probability law strictly farther than ε, not a
boundary alternative.  No logarithmic formula or limiting prior is assumed.
-/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

local instance (n : ℕ) : DecidableEq (Sample n) := Classical.decEq _

def constantSample (j n : ℕ) : Sample n := fun _ => j

theorem sampleMass_constant (p : DiscreteLaw) (j n : ℕ) :
    sampleMass p n (constantSample j n) = p.mass j ^ n := by
  simp [sampleMass, constantSample]

theorem sampleMass_pointMass (j n : ℕ) (x : Sample n) :
    sampleMass (pointMass j) n x = if x = constantSample j n then 1 else 0 := by
  classical
  by_cases hx : x = constantSample j n
  · subst x
    simp [sampleMass_constant, pointMass]
  · rw [if_neg hx]
    have hex : ∃ i, x i ≠ j := by
      by_contra h
      apply hx
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [pointMass, hi]

theorem rejectionProbability_pointMass (j : ℕ) {n : ℕ} (test : RandomizedTest n) :
    rejectionProbability (pointMass j) test = test.reject (constantSample j n) := by
  classical
  unfold rejectionProbability
  rw [tsum_eq_single (constantSample j n)]
  · simp [sampleMass_pointMass]
  · intro x hx
    simp [sampleMass_pointMass, hx]

theorem acceptanceProbability_constant_lower_bound (p : DiscreteLaw)
    (j : ℕ) {n : ℕ} (test : RandomizedTest n) :
    p.mass j ^ n * (1 - test.reject (constantSample j n)) ≤
      acceptanceProbability p test := by
  have h := (acceptance_summable p test).le_tsum (constantSample j n)
    (fun x _ => mul_nonneg (sampleMass_nonneg p n x)
      (sub_nonneg.mpr (test.le_one x)))
  simpa only [sampleMass_constant] using h

theorem totalVariation_to_pointMass (p : DiscreteLaw) (j : ℕ) :
    totalVariation p (pointMass j) = 1 - p.mass j := by
  have hsymm : totalVariation p (pointMass j) = totalVariation (pointMass j) p := by
    unfold totalVariation
    congr 1
    apply tsum_congr
    intro i
    exact abs_sub_comm _ _
  rw [hsymm, totalVariation_pointMass]

/-- The manuscript's test: reject outside the reference atom, otherwise
reject with probability `1/3`. -/
def pointMassTest (j n : ℕ) : RandomizedTest n where
  reject x := if x = constantSample j n then 1 / 3 else 1
  nonneg x := by split <;> norm_num
  le_one x := by split <;> norm_num

theorem pointMassTest_null_error (j n : ℕ) :
    rejectionProbability (pointMass j) (pointMassTest j n) = 1 / 3 := by
  rw [rejectionProbability_pointMass]
  simp [pointMassTest]

theorem pointMassTest_acceptance (p : DiscreteLaw) (j n : ℕ) :
    acceptanceProbability p (pointMassTest j n) = p.mass j ^ n * (2 / 3) := by
  classical
  unfold acceptanceProbability
  rw [tsum_eq_single (constantSample j n)]
  · norm_num [pointMassTest, sampleMass_constant]
  · intro x hx
    simp [pointMassTest, hx]

/-- An elementary upper bound on the probability of seeing no outside atom.
Its proof uses Bernoulli's inequality and `(1-ε)(1+ε) ≤ 1`. -/
theorem one_sub_pow_le_half {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (n : ℕ) (hn : 1 ≤ (n : ℝ) * ε) : (1 - ε) ^ n ≤ 1 / 2 := by
  have hp0 : 0 ≤ (1 - ε) ^ n := pow_nonneg (by linarith) n
  have hb := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ε) n
  have hprod : (1 - ε) ^ n * (1 + (n : ℝ) * ε) ≤ 1 := by
    calc
      (1 - ε) ^ n * (1 + (n : ℝ) * ε) ≤ (1 - ε) ^ n * (1 + ε) ^ n :=
        mul_le_mul_of_nonneg_left hb hp0
      _ = ((1 - ε) * (1 + ε)) ^ n := (mul_pow _ _ n).symm
      _ ≤ 1 := pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
        (by nlinarith [sq_nonneg ε])
  nlinarith

theorem pointMass_hasIdentityTest_of_mul (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) (hn : 1 ≤ (n : ℝ) * ε) :
    HasIdentityTest (pointMass j) ε n := by
  refine ⟨pointMassTest j n, ?_, ?_⟩
  · exact (pointMassTest_null_error j n).le
  · intro p hp
    rw [totalVariation_to_pointMass] at hp
    have hmass : p.mass j ≤ 1 - ε := by linarith
    have hpow : p.mass j ^ n ≤ (1 - ε) ^ n :=
      pow_le_pow_left₀ (p.nonneg j) hmass n
    have hhalf := one_sub_pow_le_half hε0.le hε1.le n hn
    rw [pointMassTest_acceptance]
    nlinarith

theorem pointMass_hasIdentityTest_ceil (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasIdentityTest (pointMass j) ε ⌈1 / ε⌉₊ := by
  apply pointMass_hasIdentityTest_of_mul j hε0 hε1
  have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (1 / ε)) hε0.le
  simpa only [div_mul_cancel₀ _ hε0.ne'] using h

/-- A normalized two-point law with mass `s` outside the reference atom. -/
def pointMassAlternative (j : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    DiscreteLaw where
  mass i := (1 - s) * (pointMass j).mass i + s * (pointMass (j + 1)).mass i
  nonneg i := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hs1) ((pointMass j).nonneg i))
    (mul_nonneg hs0 ((pointMass (j + 1)).nonneg i))
  summable := ((pointMass j).summable.mul_left (1 - s)).add
    ((pointMass (j + 1)).summable.mul_left s)
  total := by
    rw [Summable.tsum_add ((pointMass j).summable.mul_left (1 - s))
      ((pointMass (j + 1)).summable.mul_left s), tsum_mul_left, tsum_mul_left,
      (pointMass j).total, (pointMass (j + 1)).total]
    ring

theorem pointMassAlternative_mass_self (j : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (pointMassAlternative j s hs0 hs1).mass j = 1 - s := by
  simp [pointMassAlternative, pointMass]

theorem pointMassAlternative_distance (j : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    totalVariation (pointMassAlternative j s hs0 hs1) (pointMass j) = s := by
  rw [totalVariation_to_pointMass, pointMassAlternative_mass_self]
  ring

theorem pointMass_sample_mul_lower_bound (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (h : HasIdentityTest (pointMass j) ε n) : (1 / 4 : ℝ) ≤ (n : ℝ) * ε := by
  by_cases hsmall : ε ≤ 1 / 2
  · obtain ⟨test, hnull, halt⟩ := h
    rw [rejectionProbability_pointMass] at hnull
    let p := pointMassAlternative j (2 * ε) (by linarith) (by linarith)
    have hp : ε < totalVariation p (pointMass j) := by
      rw [pointMassAlternative_distance]
      linarith
    have ha := halt p hp
    have hconst := acceptanceProbability_constant_lower_bound p j test
    have hmass : p.mass j = 1 - 2 * ε := pointMassAlternative_mass_self _ _ _ _
    rw [hmass] at hconst
    have hpow0 : 0 ≤ (1 - 2 * ε) ^ n := pow_nonneg (by linarith) n
    have hprod := mul_le_mul_of_nonneg_left (show (2 / 3 : ℝ) ≤
      1 - test.reject (constantSample j n) by linarith) hpow0
    have hb := one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ 1 - 2 * ε) n
    nlinarith
  · have hn := successful_test_uses_positive_samples (pointMass j) ε hε1 n h
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmul := mul_le_mul_of_nonneg_right hn' hε0.le
    nlinarith

theorem pointMass_sample_lower_bound (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (h : HasIdentityTest (pointMass j) ε n) : (1 / ε) / 4 ≤ (n : ℝ) := by
  have hmul := pointMass_sample_mul_lower_bound j hε0 hε1 n h
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  apply (div_le_iff₀ hε0).2
  nlinarith

theorem pointMass_ceil_lower_bound (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (h : HasIdentityTest (pointMass j) ε n) : ⌈1 / ε⌉₊ ≤ 4 * n := by
  apply Nat.ceil_le.mpr
  have hreal := pointMass_sample_lower_bound j hε0 hε1 n h
  push_cast
  linarith

end IdentityTesting
