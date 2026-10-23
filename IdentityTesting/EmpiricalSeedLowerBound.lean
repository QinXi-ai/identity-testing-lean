import IdentityTesting.EmpiricalSeedCoupling
import IdentityTesting.FiniteEmbedding

/-! An actual original-model testing obstruction from empirical seed priors. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open FiniteTesting

universe u
variable {Ω : Type u} [Fintype Ω]

theorem finite_totalVariation_eq_one_sub_overlap (p q : Probability Ω) :
    FiniteTesting.totalVariation p q = 1 - ∑ x, min (p.mass x) (q.mass x) := by
  have hpoint (x : Ω) :
      |p.mass x - q.mass x| = p.mass x + q.mass x - 2 * min (p.mass x) (q.mass x) := by
    rcases le_total (p.mass x) (q.mass x) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
      ring
  simp only [FiniteTesting.totalVariation, hpoint, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, p.total, q.total]
  ring

/-- Every empirical prior member is separated whenever its support-size overlap
bound is below the remaining radius. This is uniform over all seed realizations. -/
theorem empiricalLaw_separated (q : Probability Ω) (m : ℕ) (hm : 0 < m)
    (b ε : ℝ) (hb : 0 ≤ b) (hqb : ∀ x, q.mass x ≤ b)
    (hgap : (m : ℝ) * b < 1 - ε) (seed : Fin m → Ω) :
    ε < FiniteTesting.totalVariation (empiricalLaw hm seed) q := by
  rw [finite_totalVariation_eq_one_sub_overlap]
  have h := empiricalLaw_overlap_le hm seed q.mass b q.nonneg hqb hb
  linarith

/-- A complete constructed-prior lower bound in the original model. Its
hypotheses are explicit scalar bounds on the reference masses and sample count;
no alternative family, separation, moment bound, or TV bound is assumed. -/
theorem no_identityTest_of_empirical_seeds {k : ℕ} (q : Probability (Fin k))
    (m : ℕ) (hm : 0 < m) (b ε : ℝ) (n : ℕ)
    (hb : 0 ≤ b) (hqb : ∀ x, q.mass x ≤ b)
    (hgap : (m : ℝ) * b < 1 - ε)
    (hsample : (n.choose 2 : ℝ) / (m : ℝ) < (1 : ℝ) / 3) :
    ¬ IdentityTesting.HasIdentityTest (IdentityTesting.extendFiniteLaw q) ε n := by
  apply IdentityTesting.no_identityTest_extendFiniteLaw_of_finite_prior
    (productLaw q m) (empiricalLaw hm) q ε n
  · intro seed _
    exact empiricalLaw_separated q m hm b ε hb hqb hgap seed
  · exact (seedSampleMixture_tv_le q m hm n).trans_lt hsample

end IdentityTesting.EmpiricalSeeds
