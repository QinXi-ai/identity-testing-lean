import IdentityTesting.Sampling
import IdentityTesting.FiniteIID
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact independent blocks and internal Bernoulli randomization for countable data. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

set_option maxHeartbeats 1200000 in
theorem hasSum_fin_product_nonneg {α : Type*} : ∀ (k : ℕ)
    (f : Fin k → α → ℝ) (a : Fin k → ℝ),
    (∀ j x, 0 ≤ f j x) → (∀ j, HasSum (f j) (a j)) →
      HasSum (fun x : Fin k → α => ∏ j, f j (x j)) (∏ j, a j) := by
  intro k
  induction k with
  | zero => intro f a hf hs; simp
  | succ k ih =>
    intro f a hf hs
    have ht : HasSum (fun x : Fin k → α => ∏ j : Fin k, f j.succ (x j))
        (∏ j : Fin k, a j.succ) := ih (fun j => f j.succ) (fun j => a j.succ)
      (fun j => hf j.succ) (fun j => hs j.succ)
    have hnonneg : ∀ x : Fin k → α, 0 ≤ ∏ j, f j.succ (x j) :=
      fun x => Finset.prod_nonneg (fun j _ => hf j.succ (x j))
    have hsum : Summable (fun z : α × (Fin k → α) =>
        f 0 z.1 * ∏ j, f j.succ (z.2 j)) :=
      @Summable.mul_of_nonneg α (Fin k → α) (f 0)
        (fun x : Fin k → α => ∏ j : Fin k, f j.succ (x j))
        (hs 0).summable ht.summable (hf 0) hnonneg
    have hp : HasSum (fun z : α × (Fin k → α) =>
        f 0 z.1 * ∏ j : Fin k, f j.succ (z.2 j)) (a 0 * ∏ j : Fin k, a j.succ) :=
      HasSum.mul (f := f 0) (g := fun x : Fin k → α => ∏ j : Fin k, f j.succ (x j))
        (hs 0) ht hsum
    let e : α × (Fin k → α) ≃ (Fin (k + 1) → α) := Fin.consEquiv (fun _ => α)
    apply (e.hasSum_iff).mp
    simpa only [Function.comp_apply, e, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ] using hp

def batchSampleEquiv (k n : ℕ) : Sample (k * n) ≃ (Fin k → Sample n) where
  toFun x j i := x (finProdFinEquiv (j, i))
  invFun x i := x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv x := by
    funext i
    exact congrArg x (finProdFinEquiv.apply_symm_apply i)
  right_inv x := by funext j i; simp

theorem sampleMass_batches (p : DiscreteLaw) (k n : ℕ) (x : Sample (k * n)) :
    sampleMass p (k * n) x = ∏ j, sampleMass p n (batchSampleEquiv k n x j) := by
  unfold sampleMass
  rw [← Fintype.prod_prod_type (fun ji : Fin k × Fin n =>
    p.mass (batchSampleEquiv k n x ji.1 ji.2))]
  exact (Fintype.prod_equiv finProdFinEquiv
    (fun ji : Fin k × Fin n => p.mass (batchSampleEquiv k n x ji.1 ji.2))
    (fun i => p.mass (x i)) (fun _ => rfl)).symm

def coinMass (a : ℝ) (b : Bool) : ℝ := if b then a else 1 - a

def coinLaw (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) : FiniteTesting.Probability Bool where
  mass := coinMass a
  nonneg b := by cases b <;> simp [coinMass, ha, sub_nonneg.mpr ha1]
  total := by simp [coinMass, Fintype.sum_bool]

theorem rejectionProbability_nonneg (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    0 ≤ rejectionProbability p test :=
  tsum_nonneg (fun x => mul_nonneg (sampleMass_nonneg p n x) (test.nonneg x))

theorem rejectionProbability_le_one (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    rejectionProbability p test ≤ 1 := by
  have h := rejection_add_acceptance p test
  have ha : 0 ≤ acceptanceProbability p test :=
    tsum_nonneg (fun x => mul_nonneg (sampleMass_nonneg p n x) (sub_nonneg.mpr (test.le_one x)))
  linarith

def testBitLaw (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    FiniteTesting.Probability Bool :=
  coinLaw (rejectionProbability p test) (rejectionProbability_nonneg p test)
    (rejectionProbability_le_one p test)

def conditionalBits {n : ℕ} (test : RandomizedTest n) (k : ℕ) (x : Sample (k * n)) :
    FiniteTesting.Probability (Fin k → Bool) where
  mass b := ∏ j, coinMass (test.reject (batchSampleEquiv k n x j)) (b j)
  nonneg b := Finset.prod_nonneg (fun j _ =>
    (coinLaw _ (test.nonneg _) (test.le_one _)).nonneg (b j))
  total := by
    rw [← Fintype.prod_sum]
    have hone : ∀ j : Fin k, (∑ b : Bool, coinMass (test.reject (batchSampleEquiv k n x j)) b) = 1 :=
      fun j => (coinLaw _ (test.nonneg _) (test.le_one _)).total
    simp only [hone, Finset.prod_const_one]

theorem hasSum_test_bit (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) (b : Bool) :
    HasSum (fun x => sampleMass p n x * coinMass (test.reject x) b)
      ((testBitLaw p test).mass b) := by
  cases b
  · have h := (acceptance_summable p test).hasSum
    have he := rejection_add_acceptance p test
    change HasSum _ (1 - rejectionProbability p test)
    convert h using 1
    change 1 - rejectionProbability p test = acceptanceProbability p test
    linarith
  · exact (rejection_summable p test).hasSum

set_option maxHeartbeats 1200000 in
theorem hasSum_conditional_bits (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n)
    (k : ℕ) (b : Fin k → Bool) :
    HasSum (fun x : Sample (k * n) => sampleMass p (k * n) x *
      (conditionalBits test k x).mass b)
      ((FiniteTesting.productLaw (testBitLaw p test) k).mass b) := by
  have h := hasSum_fin_product_nonneg k
    (fun j x => sampleMass p n x * coinMass (test.reject x) (b j))
    (fun j => (testBitLaw p test).mass (b j))
    (fun j x => mul_nonneg (sampleMass_nonneg p n x)
      ((coinLaw _ (test.nonneg x) (test.le_one x)).nonneg (b j)))
    (fun j => hasSum_test_bit p test (b j))
  have he := (batchSampleEquiv k n).symm.hasSum_iff
    (f := fun x : Sample (k * n) => sampleMass p (k * n) x * (conditionalBits test k x).mass b)
    (a := (FiniteTesting.productLaw (testBitLaw p test) k).mass b)
  apply he.mp
  convert h using 1
  funext x
  simp only [Function.comp_apply]
  rw [sampleMass_batches]
  simp only [conditionalBits, Equiv.apply_symm_apply, Finset.prod_mul_distrib]

/-- Exact marginalization of independent internal coins and disjoint IID batches. -/
theorem conditional_bits_expectation (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n)
    (k : ℕ) (f : (Fin k → Bool) → ℝ) :
    (∑' x : Sample (k * n), sampleMass p (k * n) x *
      FiniteIID.mean (conditionalBits test k x) f) =
      FiniteIID.mean (FiniteTesting.productLaw (testBitLaw p test) k) f := by
  simp only [FiniteIID.mean, Finset.mul_sum, ← mul_assoc]
  rw [Summable.tsum_finsetSum (fun b _ => (hasSum_conditional_bits p test k b).summable.mul_right (f b))]
  apply Finset.sum_congr rfl
  intro b _
  exact ((hasSum_conditional_bits p test k b).mul_right (f b)).tsum_eq

end IdentityTesting
