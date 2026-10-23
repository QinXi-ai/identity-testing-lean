import IdentityTesting.FiniteChiSquare

/-!
# A conditional finite-prior second-moment lower-bound interface

This module connects an actual finite prior and its actual fixed-size IID
likelihood moment to the testing obstruction.  The prior, the strict separation
of its positive-weight alternatives, and the numerical pairwise-moment bound are
still hypotheses: no prior construction or moment estimate is asserted here.
In particular, this interface is not the manuscript's main complexity theorem.
-/

noncomputable section

namespace IdentityTesting.FiniteMomentLowerBound

open scoped BigOperators
open IdentityTesting.FiniteTesting IdentityTesting.FiniteChiSquare

universe u v

variable {Ω : Type u} [Fintype Ω] {I : Type v} [Fintype I]

/-- A positive one-observation reference law has a positive IID sample law. -/
theorem productLaw_mass_pos (q : Probability Ω) (hq : ∀ x, 0 < q.mass x)
    (n : ℕ) (sample : Fin n → Ω) :
    0 < (productLaw q n).mass sample := by
  simp only [productLaw_mass]
  exact Finset.prod_pos fun j _ => hq (sample j)

/-- The threshold `13/9` on the actual second moment gives sample TV `< 1/3`. -/
theorem iid_mixture_totalVariation_lt_one_third (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) (n : ℕ)
    (hq : ∀ x, 0 < q.mass x)
    (hmoment :
      (∑ i, ∑ j, weights.mass i * weights.mass j *
        (likelihoodInner (family i) (family j) q) ^ n) < (13 : ℝ) / 9) :
    totalVariation (mixture weights (fun i => productLaw (family i) n))
      (productLaw q n) < (1 : ℝ) / 3 := by
  let Q := mixture weights (fun i => productLaw (family i) n)
  let qn := productLaw q n
  have hidentity := one_add_chiSquare_iid_mixture weights family q n
  have hchi : chiSquare Q qn < (4 : ℝ) / 9 := by
    dsimp [Q, qn]
    linarith only [hidentity, hmoment]
  have hTV := totalVariation_sq_le_chiSquare_div_four Q qn
    (fun sample => productLaw_mass_pos q hq n sample)
  have hTVsq : (totalVariation Q qn) ^ 2 < (1 : ℝ) / 9 := by
    linarith only [hTV, hchi]
  change totalVariation Q qn < (1 : ℝ) / 3
  by_contra hnot
  have hlarge : (1 : ℝ) / 3 ≤ totalVariation Q qn := le_of_not_gt hnot
  have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 3) hlarge
  nlinarith only [hTVsq, hmul]

/-- Conditional rejection-probability formulation.  The pairwise moment and
the separated finite prior remain explicit inputs. -/
theorem no_uniform_rejection_test_of_pair_moment_lt (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) (ε : ℝ) (n : ℕ)
    (hq : ∀ x, 0 < q.mass x)
    (hseparated : ∀ i, 0 < weights.mass i → ε < totalVariation (family i) q)
    (hmoment :
      (∑ i, ∑ j, weights.mass i * weights.mass j *
        (likelihoodInner (family i) (family j) q) ^ n) < (13 : ℝ) / 9) :
    ¬ ∃ test : RandomizedTest (Fin n → Ω),
      expectation (productLaw q n) test ≤ (1 : ℝ) / 3 ∧
      ∀ p : Probability Ω, ε < totalVariation p q →
        (2 : ℝ) / 3 ≤ expectation (productLaw p n) test := by
  exact finite_iid_prior_obstruction_on_support weights family q ε n hseparated
    (iid_mixture_totalVariation_lt_one_third weights family q n hq hmoment)

/-- No identity test can have both errors at most `1/3` under the explicit
finite-prior separation and actual pairwise-moment hypotheses. -/
theorem no_identity_test_of_pair_moment_lt (weights : Probability I)
    (family : I → Probability Ω) (q : Probability Ω) (ε : ℝ) (n : ℕ)
    (hq : ∀ x, 0 < q.mass x)
    (hseparated : ∀ i, 0 < weights.mass i → ε < totalVariation (family i) q)
    (hmoment :
      (∑ i, ∑ j, weights.mass i * weights.mass j *
        (likelihoodInner (family i) (family j) q) ^ n) < (13 : ℝ) / 9) :
    ¬ ∃ test : RandomizedTest (Fin n → Ω),
      expectation (productLaw q n) test ≤ (1 : ℝ) / 3 ∧
      ∀ p : Probability Ω, ε < totalVariation p q →
        1 - expectation (productLaw p n) test ≤ (1 : ℝ) / 3 := by
  rintro ⟨test, hnull, halt⟩
  apply no_uniform_rejection_test_of_pair_moment_lt weights family q ε n hq
    hseparated hmoment
  refine ⟨test, hnull, ?_⟩
  intro p hp
  have h := halt p hp
  linarith

end IdentityTesting.FiniteMomentLowerBound
