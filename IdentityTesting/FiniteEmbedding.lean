import IdentityTesting.FiniteMomentLowerBound
import IdentityTesting.Sampling

/-!
# Embedding actual finite lower-bound instances in the countable model

Finite laws on `Fin k` are extended by zero to the natural-number labels.  The
extension preserves TV and the actual IID test probabilities.  Consequently a
finite-prior lower bound applies to the original `HasIdentityTest` predicate for
the extended reference law.  A separated prior and its pairwise-moment estimate
remain explicit hypotheses; no such construction or estimate is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting

private theorem hasSum_of_finite_injective {α β : Type*} [Fintype α]
    (e : α → β) (he : Function.Injective e) (f : β → ℝ)
    (hf : ∀ x, x ∉ Set.range e → f x = 0) :
    HasSum f (∑ a, f (e a)) := by
  have hfinite : HasSum (f ∘ e) (∑ a, f (e a)) := by
    simpa only [Function.comp_apply] using hasSum_fintype (fun a => f (e a))
  exact (he.hasSum_iff (f := f) (a := ∑ a, f (e a)) hf).mp hfinite

/-- Extend a finite mass vector by zero outside its label range. -/
def extendFiniteMass {k : ℕ} (p : FiniteTesting.Probability (Fin k)) (i : ℕ) : ℝ :=
  if hi : i < k then p.mass ⟨i, hi⟩ else 0

@[simp] theorem extendFiniteMass_val {k : ℕ} (p : FiniteTesting.Probability (Fin k))
    (i : Fin k) : extendFiniteMass p i.val = p.mass i := by
  simp [extendFiniteMass]

private theorem extendFiniteMass_hasSum {k : ℕ} (p : FiniteTesting.Probability (Fin k)) :
    HasSum (extendFiniteMass p) 1 := by
  have hzero : ∀ i, i ∉ Set.range (fun j : Fin k => j.val) → extendFiniteMass p i = 0 := by
    intro i hi
    have hnot : ¬ i < k := fun h => hi ⟨⟨i, h⟩, rfl⟩
    simp [extendFiniteMass, hnot]
  have h := hasSum_of_finite_injective (fun j : Fin k => j.val) Fin.val_injective
    (extendFiniteMass p) hzero
  simpa only [extendFiniteMass_val, p.total] using h

/-- The normalized countable law obtained from an actual finite law. -/
def extendFiniteLaw {k : ℕ} (p : FiniteTesting.Probability (Fin k)) : DiscreteLaw where
  mass := extendFiniteMass p
  nonneg i := by
    unfold extendFiniteMass
    split
    · exact p.nonneg _
    · exact le_rfl
  summable := (extendFiniteMass_hasSum p).summable
  total := (extendFiniteMass_hasSum p).tsum_eq

@[simp] theorem extendFiniteLaw_mass_val {k : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (i : Fin k) :
    (extendFiniteLaw p).mass i.val = p.mass i :=
  extendFiniteMass_val p i

theorem extendFiniteLaw_mass_of_not_lt {k : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (i : ℕ) (hi : ¬ i < k) :
    (extendFiniteLaw p).mass i = 0 := by
  change extendFiniteMass p i = 0
  simp [extendFiniteMass, hi]

/-- Zero extension preserves the original total-variation normalization exactly. -/
theorem totalVariation_extendFiniteLaw {k : ℕ}
    (p q : FiniteTesting.Probability (Fin k)) :
    totalVariation (extendFiniteLaw p) (extendFiniteLaw q) =
      FiniteTesting.totalVariation p q := by
  have hzero : ∀ i, i ∉ Set.range (fun j : Fin k => j.val) →
      |(extendFiniteLaw p).mass i - (extendFiniteLaw q).mass i| = 0 := by
    intro i hi
    have hnot : ¬ i < k := fun h => hi ⟨⟨i, h⟩, rfl⟩
    rw [extendFiniteLaw_mass_of_not_lt p i hnot, extendFiniteLaw_mass_of_not_lt q i hnot]
    simp
  have h := hasSum_of_finite_injective (fun j : Fin k => j.val) Fin.val_injective
    (fun i => |(extendFiniteLaw p).mass i - (extendFiniteLaw q).mass i|) hzero
  have hsum : (∑' i, |(extendFiniteLaw p).mass i - (extendFiniteLaw q).mass i|) =
      ∑ j : Fin k, |p.mass j - q.mass j| := by
    simpa only [extendFiniteLaw_mass_val] using h.tsum_eq
  unfold totalVariation FiniteTesting.totalVariation
  rw [hsum]
  ring

/-- Embed every coordinate of a finite sample into the natural-number labels. -/
def embedFiniteSample {k n : ℕ} (sample : Fin n → Fin k) : Sample n :=
  fun j => (sample j).val

theorem embedFiniteSample_injective (k n : ℕ) :
    Function.Injective (embedFiniteSample (k := k) (n := n)) := by
  intro x y h
  funext j
  apply Fin.ext
  exact congrFun h j

theorem sampleMass_extendFiniteLaw_embed {k n : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (sample : Fin n → Fin k) :
    sampleMass (extendFiniteLaw p) n (embedFiniteSample sample) =
      (FiniteTesting.productLaw p n).mass sample := by
  simp only [sampleMass, embedFiniteSample, extendFiniteLaw_mass_val,
    FiniteTesting.productLaw_mass]

theorem sampleMass_extendFiniteLaw_zero_off_range {k n : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (sample : Sample n)
    (hoff : sample ∉ Set.range (embedFiniteSample (k := k) (n := n))) :
    sampleMass (extendFiniteLaw p) n sample = 0 := by
  classical
  have hnotall : ¬ ∀ j : Fin n, sample j < k := by
    intro hall
    exact hoff ⟨fun j => ⟨sample j, hall j⟩, rfl⟩
  obtain ⟨j, hj⟩ := not_forall.mp hnotall
  unfold sampleMass
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (extendFiniteLaw_mass_of_not_lt p (sample j) hj)

/-- Restrict any original randomized test to the embedded finite sample tuples. -/
def restrictFiniteTest {k n : ℕ} (test : RandomizedTest n) :
    FiniteTesting.RandomizedTest (Fin n → Fin k) where
  reject sample := test.reject (embedFiniteSample sample)
  nonneg sample := test.nonneg (embedFiniteSample sample)
  le_one sample := test.le_one (embedFiniteSample sample)

/-- The actual countable IID rejection probability equals its finite restriction. -/
theorem rejectionProbability_extendFiniteLaw {k n : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (test : RandomizedTest n) :
    rejectionProbability (extendFiniteLaw p) test =
      FiniteTesting.expectation (FiniteTesting.productLaw p n) (restrictFiniteTest test) := by
  have hzero : ∀ sample, sample ∉ Set.range (embedFiniteSample (k := k) (n := n)) →
      sampleMass (extendFiniteLaw p) n sample * test.reject sample = 0 := by
    intro sample hoff
    rw [sampleMass_extendFiniteLaw_zero_off_range p sample hoff, zero_mul]
  have h := hasSum_of_finite_injective (embedFiniteSample (k := k) (n := n))
    (embedFiniteSample_injective k n)
    (fun sample => sampleMass (extendFiniteLaw p) n sample * test.reject sample) hzero
  unfold rejectionProbability
  rw [h.tsum_eq]
  unfold FiniteTesting.expectation
  apply Finset.sum_congr rfl
  intro sample _
  simp only [sampleMass_extendFiniteLaw_embed, restrictFiniteTest]

theorem acceptanceProbability_extendFiniteLaw {k n : ℕ}
    (p : FiniteTesting.Probability (Fin k)) (test : RandomizedTest n) :
    acceptanceProbability (extendFiniteLaw p) test =
      1 - FiniteTesting.expectation (FiniteTesting.productLaw p n) (restrictFiniteTest test) := by
  have h := rejection_add_acceptance (extendFiniteLaw p) test
  rw [rejectionProbability_extendFiniteLaw] at h
  linarith

/-- The finite-prior obstruction now excludes actual countable-space tests at
the constructed reference law; all finite alternatives are extended internally. -/
theorem no_identityTest_extendFiniteLaw_of_finite_prior {k : ℕ} {I : Type*} [Fintype I]
    (weights : FiniteTesting.Probability I)
    (family : I → FiniteTesting.Probability (Fin k))
    (q : FiniteTesting.Probability (Fin k)) (ε : ℝ) (n : ℕ)
    (hseparated : ∀ i, 0 < weights.mass i → ε < FiniteTesting.totalVariation (family i) q)
    (hTV : FiniteTesting.totalVariation
      (FiniteTesting.mixture weights (fun i => FiniteTesting.productLaw (family i) n))
      (FiniteTesting.productLaw q n) < (1 : ℝ) / 3) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  rintro ⟨test, hnull, halt⟩
  apply FiniteTesting.finite_iid_prior_obstruction_on_support weights family q ε n
    hseparated hTV
  refine ⟨restrictFiniteTest test, ?_, ?_⟩
  · rw [← rejectionProbability_extendFiniteLaw q test]
    exact hnull
  · intro p hp
    have hsep : ε < totalVariation (extendFiniteLaw p) (extendFiniteLaw q) := by
      rw [totalVariation_extendFiniteLaw]
      exact hp
    have herror := halt (extendFiniteLaw p) hsep
    rw [acceptanceProbability_extendFiniteLaw] at herror
    linarith

/-- Conditional moment lower bound in the original countable testing model.
The separated prior and its actual pairwise-moment estimate remain inputs. -/
theorem no_identityTest_extendFiniteLaw_of_pair_moment_lt {k : ℕ} {I : Type*} [Fintype I]
    (weights : FiniteTesting.Probability I)
    (family : I → FiniteTesting.Probability (Fin k))
    (q : FiniteTesting.Probability (Fin k)) (ε : ℝ) (n : ℕ)
    (hq : ∀ x, 0 < q.mass x)
    (hseparated : ∀ i, 0 < weights.mass i → ε < FiniteTesting.totalVariation (family i) q)
    (hmoment :
      (∑ i, ∑ j, weights.mass i * weights.mass j *
        (FiniteChiSquare.likelihoodInner (family i) (family j) q) ^ n) < (13 : ℝ) / 9) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  exact no_identityTest_extendFiniteLaw_of_finite_prior weights family q ε n hseparated
    (FiniteMomentLowerBound.iid_mixture_totalVariation_lt_one_third weights family q n hq hmoment)

end IdentityTesting
