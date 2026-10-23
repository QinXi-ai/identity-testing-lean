import IdentityTesting.Sampling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Arbitrary measurable priors on laws on the original natural-number alphabet. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace IdentityTesting

local instance (n : ℕ) : Countable (Sample n) := by unfold Sample; infer_instance

variable {Θ : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsProbabilityMeasure μ]
  (p : Θ → DiscreteLaw)

def priorSampleMass (n : ℕ) (x : Sample n) : ℝ := ∫ θ, sampleMass (p θ) n x ∂μ

theorem sampleMass_measurable
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) (n : ℕ) (x : Sample n) :
    Measurable (fun θ => sampleMass (p θ) n x) := by
  exact Finset.measurable_prod _ (fun i _ => hp (x i))

theorem priorSampleMass_nonneg (n : ℕ) (x : Sample n) : 0 ≤ priorSampleMass μ p n x :=
  integral_nonneg (fun θ => sampleMass_nonneg (p θ) n x)

theorem priorSampleMass_hasSum
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) (n : ℕ) :
    HasSum (priorSampleMass μ p n) 1 := by
  have h := hasSum_integral_of_dominated_convergence
    (fun x θ => sampleMass (p θ) n x)
    (fun x => (sampleMass_measurable p hp n x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_of_nonneg (sampleMass_nonneg (p θ) n x)]))
    (Filter.Eventually.of_forall (fun θ => (sampleMass_hasSum (p θ) n).summable))
    (show Integrable (fun θ => ∑' x, sampleMass (p θ) n x) μ by
      simp_rw [(sampleMass_hasSum _ _).tsum_eq]; exact integrable_const 1)
    (Filter.Eventually.of_forall (fun θ => sampleMass_hasSum (p θ) n))
  simpa [priorSampleMass] using h

theorem acceptanceProbability_nonneg (q : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    0 ≤ acceptanceProbability q test :=
  tsum_nonneg (fun x => mul_nonneg (sampleMass_nonneg q n x)
    (sub_nonneg.mpr (test.le_one x)))

theorem acceptanceProbability_le_one (q : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    acceptanceProbability q test ≤ 1 := by
  have hr : 0 ≤ rejectionProbability q test :=
    tsum_nonneg (fun x => mul_nonneg (sampleMass_nonneg q n x) (test.nonneg x))
  linarith [rejection_add_acceptance q test]

theorem prior_acceptance_integrable
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) {n : ℕ} (test : RandomizedTest n) :
    Integrable (fun θ => acceptanceProbability (p θ) test) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
  · apply aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset (Sample n)))
      (fun s => s.aestronglyMeasurable_fun_sum (fun x _ =>
        ((sampleMass_measurable p hp n x).mul_const
          (1 - test.reject x)).aestronglyMeasurable))
    exact Filter.Eventually.of_forall (fun θ => (acceptance_summable (p θ) test).hasSum)
  · exact Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_of_nonneg (acceptanceProbability_nonneg (p θ) test)]
      exact acceptanceProbability_le_one (p θ) test)

theorem prior_average_acceptance
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) {n : ℕ} (test : RandomizedTest n) :
    (∑' x, priorSampleMass μ p n x * (1 - test.reject x)) =
      ∫ θ, acceptanceProbability (p θ) test ∂μ := by
  have h := hasSum_integral_of_dominated_convergence
    (fun x θ => sampleMass (p θ) n x)
    (fun x => ((sampleMass_measurable p hp n x).mul_const
      (1 - test.reject x)).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_of_nonneg (mul_nonneg (sampleMass_nonneg (p θ) n x)
        (sub_nonneg.mpr (test.le_one x)))]
      exact mul_le_of_le_one_right (sampleMass_nonneg (p θ) n x)
        (by linarith [test.nonneg x])))
    (Filter.Eventually.of_forall (fun θ => (sampleMass_hasSum (p θ) n).summable))
    (show Integrable (fun θ => ∑' x, sampleMass (p θ) n x) μ by
      simp_rw [(sampleMass_hasSum _ _).tsum_eq]; exact integrable_const 1)
    (Filter.Eventually.of_forall (fun θ => (acceptance_summable (p θ) test).hasSum))
  simpa only [priorSampleMass, integral_mul_const] using h.tsum_eq

def priorSampleTotalVariation (q : DiscreteLaw) (n : ℕ) : ℝ :=
  (∑' x, |priorSampleMass μ p n x - sampleMass q n x|) / 2

theorem prior_acceptance_summable
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) {n : ℕ} (test : RandomizedTest n) :
    Summable (fun x => priorSampleMass μ p n x * (1 - test.reject x)) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (priorSampleMass_nonneg μ p n x) (sub_nonneg.mpr (test.le_one x)))
    (fun x => mul_le_of_le_one_right (priorSampleMass_nonneg μ p n x)
      (by linarith [test.nonneg x])) (priorSampleMass_hasSum μ p hp n).summable

/-- The original null error plus the integral of alternative errors, for any
measurable probability prior and any number of observations, including zero. -/
theorem measure_prior_error_bound
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) (q : DiscreteLaw)
    {n : ℕ} (test : RandomizedTest n) :
    1 - priorSampleTotalVariation μ p q n ≤ rejectionProbability q test +
      ∫ θ, acceptanceProbability (p θ) test ∂μ := by
  let a := priorSampleMass μ p n
  let b := sampleMass q n
  have ha : Summable a := (priorSampleMass_hasSum μ p hp n).summable
  have hb : Summable b := (sampleMass_hasSum q n).summable
  have hab : Summable (fun x => |a x - b x|) := (ha.sub hb).abs
  have hpoint : ∀ x, (a x + b x - |a x - b x|) / 2 ≤
      b x * test.reject x + a x * (1 - test.reject x) := by
    intro x
    by_cases h : 0 ≤ a x - b x
    · rw [abs_of_nonneg h]
      have := mul_nonneg h (sub_nonneg.mpr (test.le_one x))
      nlinarith
    · rw [abs_of_nonpos (le_of_not_ge h)]
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (test.nonneg x)
      nlinarith
  have hsum := (((ha.add hb).sub hab).div_const 2).tsum_le_tsum hpoint
    ((rejection_summable q test).add (prior_acceptance_summable μ p hp test))
  rw [tsum_div_const, (ha.add hb).tsum_sub hab, ha.tsum_add hb,
    (priorSampleMass_hasSum μ p hp n).tsum_eq, (sampleMass_hasSum q n).tsum_eq,
    (rejection_summable q test).tsum_add (prior_acceptance_summable μ p hp test),
    prior_average_acceptance μ p hp test] at hsum
  change 1 - (∑' x, |a x - b x|) / 2 ≤ _
  change (1 + 1 - ∑' x, |a x - b x|) / 2 ≤ _ at hsum
  unfold rejectionProbability
  linarith

/-- Lemma `lem:prior`, with an arbitrary probability measure prior. The support
condition is only almost everywhere, which includes ordinary supported priors. -/
theorem no_identityTest_of_measure_prior
    (hp : ∀ i, Measurable (fun θ => (p θ).mass i)) (q : DiscreteLaw) (ε : ℝ) (n : ℕ)
    (hfar : ∀ᵐ θ ∂μ, ε < totalVariation (p θ) q)
    (htv : priorSampleTotalVariation μ p q n < 1 / 3) :
    ¬ HasIdentityTest q ε n := by
  rintro ⟨test, hnull, halt⟩
  have havg : (∫ θ, acceptanceProbability (p θ) test ∂μ) ≤ 1 / 3 := by
    have h := integral_mono_ae (prior_acceptance_integrable μ p hp test)
      (integrable_const (1 / 3 : ℝ)) (hfar.mono (fun θ hθ => halt (p θ) hθ))
    simpa using h
  have h := measure_prior_error_bound μ p hp q test
  linarith

end IdentityTesting
