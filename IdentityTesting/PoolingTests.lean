import IdentityTesting.CountablePooling
import IdentityTesting.Sampling

/-!
# Pulling finite pooled tests back to the original countable sample space

The sample-fiber mass and rejection-probability identities below use the actual
IID laws.  The transfer theorem constructs the original randomized test and
uses the strict-radius loss proved for the actual pooled distributions.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting

/-- Pool every coordinate of a fixed-size sample. -/
def samplePoolMap (s : Finset ℕ) (n : ℕ) (sample : Sample n) : Fin n → PoolLabel s :=
  fun j => poolMap s (sample j)

/-- The actual countable-space test obtained by applying a finite pooled test. -/
def pullbackPooledTest (s : Finset ℕ) {n : ℕ}
    (test : FiniteTesting.RandomizedTest (Fin n → PoolLabel s)) : RandomizedTest n where
  reject sample := test.reject (samplePoolMap s n sample)
  nonneg sample := test.nonneg (samplePoolMap s n sample)
  le_one sample := test.le_one (samplePoolMap s n sample)

private theorem hasSum_mul_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    HasSum (fun z : α × β => f z.1 * g z.2) (a * b) := by
  exact HasSum.mul hf hg (Summable.mul_of_nonneg hf.summable hg.summable hf0 hg0)

set_option maxHeartbeats 800000 in
/-- A finite product of nonnegative summable coordinate masses has the product sum. -/
private theorem hasSum_fin_prod_varying : ∀ (n : ℕ)
    (a : Fin n → ℕ → ℝ) (b : Fin n → ℝ),
    (∀ j i, 0 ≤ a j i) → (∀ j, HasSum (a j) (b j)) →
      HasSum (fun sample : Fin n → ℕ => ∏ j, a j (sample j)) (∏ j, b j) := by
  intro n
  induction n with
  | zero =>
      intro a b _ _
      simp
  | succ n ih =>
      intro a b ha hb
      have htail := ih (fun j => a j.succ) (fun j => b j.succ)
        (fun j i => ha j.succ i) (fun j => hb j.succ)
      dsimp only at htail
      have hnonneg : 0 ≤ (fun sample : Fin n → ℕ => ∏ j, a j.succ (sample j)) := by
        intro sample
        exact Finset.prod_nonneg fun j _ => ha j.succ (sample j)
      have hprod := hasSum_mul_nonneg (hb 0) htail (ha 0) hnonneg
      let f : (Fin (n + 1) → ℕ) → ℝ := fun sample => ∏ j, a j (sample j)
      let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
      have hcomp : f ∘ e =
          (fun z : ℕ × (Fin n → ℕ) => a 0 z.1 * ∏ j, a j.succ (z.2 j)) := by
        funext z
        simp only [Function.comp_apply, f, e, Fin.consEquiv_apply,
          Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hcons : HasSum (f ∘ e) (b 0 * ∏ j : Fin n, b j.succ) := by
        rw [hcomp]
        exact hprod
      rw [Fin.prod_univ_succ b]
      exact (e.hasSum_iff (f := f) (a := b 0 * ∏ j : Fin n, b j.succ)).mp hcons

private theorem hasSum_pool_fiber (p : DiscreteLaw) (s : Finset ℕ) (y : PoolLabel s) :
    HasSum (fun i : ℕ => if poolMap s i = y then p.mass i else 0)
      ((pooledLaw p s).mass y) := by
  classical
  have hsummable : Summable (fun i : ℕ => if poolMap s i = y then p.mass i else 0) := by
    apply Summable.of_nonneg_of_le _ _ p.summable
    · intro i
      split
      · exact p.nonneg i
      · exact le_rfl
    · intro i
      split
      · exact le_rfl
      · exact p.nonneg i
  have hvalue : (∑' i : ℕ, if poolMap s i = y then p.mass i else 0) =
      (pooledLaw p s).mass y := by
    rw [pooledLaw_mass_fiber]
    symm
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
      (tsum_subtype {i | poolMap s i = y} p.mass)
  rw [← hvalue]
  exact hsummable.hasSum

/-- The finite IID law is exactly the pushforward of the actual countable IID law. -/
theorem sampleMass_pool_fiber (p : DiscreteLaw) (s : Finset ℕ) (n : ℕ)
    (y : Fin n → PoolLabel s) :
    (∑' sample : {sample : Sample n // samplePoolMap s n sample = y},
      sampleMass p n sample) =
        (FiniteTesting.productLaw (pooledLaw p s) n).mass y := by
  classical
  have hprod := hasSum_fin_prod_varying n
    (fun j i => if poolMap s i = y j then p.mass i else 0)
    (fun j => (pooledLaw p s).mass (y j))
    (fun j i => by
      dsimp only
      split
      · exact p.nonneg i
      · exact le_rfl)
    (fun j => hasSum_pool_fiber p s (y j))
  dsimp only at hprod
  have hfun : (fun sample : Sample n =>
      ∏ j, if poolMap s (sample j) = y j then p.mass (sample j) else 0) =
      (fun sample : Sample n =>
        if samplePoolMap s n sample = y then sampleMass p n sample else 0) := by
    funext sample
    by_cases hsample : samplePoolMap s n sample = y
    · have hpoint : ∀ j, poolMap s (sample j) = y j := fun j => congrFun hsample j
      simp [hpoint, hsample, sampleMass]
    · rw [if_neg hsample]
      have hexists : ∃ j, poolMap s (sample j) ≠ y j := by
        by_contra hnone
        push_neg at hnone
        exact hsample (funext hnone)
      obtain ⟨j, hj⟩ := hexists
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  calc
    (∑' sample : {sample : Sample n // samplePoolMap s n sample = y},
        sampleMass p n sample) =
        ∑' sample : Sample n,
          if samplePoolMap s n sample = y then sampleMass p n sample else 0 := by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
        (tsum_subtype {sample : Sample n | samplePoolMap s n sample = y} (sampleMass p n))
    _ = ∑' sample : Fin n → ℕ,
        ∏ j, if poolMap s (sample j) = y j then p.mass (sample j) else 0 := by
      exact tsum_congr fun sample => (congrFun hfun sample).symm
    _ = _ := by
      simpa only [FiniteTesting.productLaw_mass] using hprod.tsum_eq

/-- Applying the finite test after coordinatewise pooling preserves rejection probability. -/
theorem rejectionProbability_pullbackPooledTest (p : DiscreteLaw) (s : Finset ℕ) {n : ℕ}
    (test : FiniteTesting.RandomizedTest (Fin n → PoolLabel s)) :
    rejectionProbability p (pullbackPooledTest s test) =
      FiniteTesting.expectation (FiniteTesting.productLaw (pooledLaw p s) n) test := by
  classical
  have hgroup := ((rejection_summable p (pullbackPooledTest s test)).hasSum.tsum_fiberwise
    (samplePoolMap s n)).tsum_eq
  unfold rejectionProbability
  rw [← hgroup, tsum_fintype]
  unfold FiniteTesting.expectation
  apply Finset.sum_congr rfl
  intro y _
  change (∑' sample : {sample : Sample n // samplePoolMap s n sample = y},
      sampleMass p n sample * test.reject (samplePoolMap s n sample)) =
    (FiniteTesting.productLaw (pooledLaw p s) n).mass y * test.reject y
  calc
    (∑' sample : {sample : Sample n // samplePoolMap s n sample = y},
        sampleMass p n sample * test.reject (samplePoolMap s n sample)) =
        (∑' sample : {sample : Sample n // samplePoolMap s n sample = y},
          sampleMass p n sample) * test.reject y := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro sample
      rw [sample.property]
    _ = _ := by rw [sampleMass_pool_fiber]

theorem acceptanceProbability_pullbackPooledTest (p : DiscreteLaw) (s : Finset ℕ) {n : ℕ}
    (test : FiniteTesting.RandomizedTest (Fin n → PoolLabel s)) :
    acceptanceProbability p (pullbackPooledTest s test) =
      1 - FiniteTesting.expectation (FiniteTesting.productLaw (pooledLaw p s) n) test := by
  have htotal := rejection_add_acceptance p (pullbackPooledTest s test)
  rw [rejectionProbability_pullbackPooledTest] at htotal
  linarith

/-- A finite test at the radius reduced by the reference residual mass gives an
actual countable identity test at the original strict radius. -/
theorem hasIdentityTest_of_pooled_test (q : DiscreteLaw) (s : Finset ℕ)
    (ε : ℝ) (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → PoolLabel s))
    (hnull : FiniteTesting.expectation
      (FiniteTesting.productLaw (pooledLaw q s) n) test ≤ (1 : ℝ) / 3)
    (halt : ∀ p : FiniteTesting.Probability (PoolLabel s),
      ε - residualMass q s < FiniteTesting.totalVariation p (pooledLaw q s) →
        1 - FiniteTesting.expectation (FiniteTesting.productLaw p n) test ≤ (1 : ℝ) / 3) :
    HasIdentityTest q ε n := by
  refine ⟨pullbackPooledTest s test, ?_, ?_⟩
  · rw [rejectionProbability_pullbackPooledTest]
    exact hnull
  · intro p hp
    rw [acceptanceProbability_pullbackPooledTest]
    exact halt (pooledLaw p s) (strict_alternative_survives_pooling p q s ε hp)

end IdentityTesting
