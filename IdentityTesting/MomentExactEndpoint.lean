import IdentityTesting.PointMassExact
import IdentityTesting.MomentTestingGeometry
import IdentityTesting.FiniteAllocationUpper

/-! Exact small-overlap endpoint for finite reference laws, with observations
and alternatives on the original natural-number alphabet. The strict-radius
necessity is proved using actual zero-label mixtures, not a supplied prior. -/

noncomputable section
open scoped BigOperators Topology
open Filter Set
namespace IdentityTesting

/-- Keep mass `s` of the reference and put the remainder at one label. -/
def endpointMixture (q : DiscreteLaw) (z : ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : DiscreteLaw where
  mass i := s * q.mass i + (1 - s) * (pointMass z).mass i
  nonneg i := add_nonneg (mul_nonneg hs0 (q.nonneg i))
    (mul_nonneg (sub_nonneg.mpr hs1) ((pointMass z).nonneg i))
  summable := (q.summable.mul_left s).add ((pointMass z).summable.mul_left (1 - s))
  total := by
    rw [Summable.tsum_add (q.summable.mul_left s)
      ((pointMass z).summable.mul_left (1 - s)), tsum_mul_left, tsum_mul_left,
      q.total, (pointMass z).total]
    ring

theorem endpointMixture_distance (q : DiscreteLaw) (z : ℕ) (hz : q.mass z = 0)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    totalVariation (endpointMixture q z s hs0 hs1) q = 1 - s := by
  have hmin (i : ℕ) : min ((endpointMixture q z s hs0 hs1).mass i) (q.mass i) =
      s * q.mass i := by
    by_cases hi : i = z
    · subst i
      simp only [endpointMixture, pointMass, hz, ite_true, mul_zero, mul_one, zero_add]
      exact min_eq_right (sub_nonneg.mpr hs1)
    · simp only [endpointMixture, pointMass, if_neg hi, mul_zero, add_zero]
      exact min_eq_left (mul_le_of_le_one_left (q.nonneg i) hs1)
  rw [totalVariation_eq_one_sub_overlap]
  simp_rw [hmin]
  rw [tsum_mul_left, q.total, mul_one]

theorem endpointMixture_acceptance_lower (q : DiscreteLaw) (z : ℕ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {n : ℕ} (test : RandomizedTest n) :
    s ^ n * acceptanceProbability q test ≤
      acceptanceProbability (endpointMixture q z s hs0 hs1) test := by
  have hsample (x : Sample n) : s ^ n * sampleMass q n x ≤
      sampleMass (endpointMixture q z s hs0 hs1) n x := by
    have h : (∏ i, s * q.mass (x i)) ≤
        ∏ i, (endpointMixture q z s hs0 hs1).mass (x i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg hs0 (q.nonneg _)
      · intro i _
        exact le_add_of_nonneg_right
          (mul_nonneg (sub_nonneg.mpr hs1) ((pointMass z).nonneg _))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, sampleMass] using h
  have h := ((acceptance_summable q test).mul_left (s ^ n)).tsum_le_tsum
    (fun x => by
      have h := mul_le_mul_of_nonneg_right (hsample x)
        (sub_nonneg.mpr (test.le_one x))
      simpa only [mul_assoc] using h)
    (acceptance_summable (endpointMixture q z s hs0 hs1) test)
  simpa only [tsum_mul_left, acceptanceProbability] using h

/-- Any available zero-reference label forces the exact endpoint power bound. -/
theorem zero_label_pow_necessary (q : DiscreteLaw) (z : ℕ) (hz : q.mass z = 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ)
    (ht : HasIdentityTest q (1 - δ) n) : δ ^ n ≤ (1 : ℝ) / 2 := by
  obtain ⟨test, hnull, halt⟩ := ht
  have hnullacc : (2 : ℝ) / 3 ≤ acceptanceProbability q test := by
    linarith [rejection_add_acceptance q test]
  have hstrict (s : ℝ) (hs0 : 0 < s) (hsδ : s < δ) : s ^ n ≤ (1 : ℝ) / 2 := by
    have hs1 : s ≤ 1 := (hsδ.trans hδ1).le
    let p := endpointMixture q z s hs0.le hs1
    have hp : 1 - δ < totalVariation p q := by
      rw [endpointMixture_distance q z hz]
      linarith
    have ha := halt p hp
    have hl := endpointMixture_acceptance_lower q z s hs0.le hs1 test
    have hm := mul_le_mul_of_nonneg_left hnullacc (pow_nonneg hs0.le n)
    change acceptanceProbability p test ≤ _ at ha
    change s ^ n * acceptanceProbability q test ≤ acceptanceProbability p test at hl
    nlinarith
  have hlim : Tendsto (fun s : ℝ => s ^ n) (𝓝[<] δ) (𝓝 (δ ^ n)) :=
    ((continuous_id.pow n).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hδ0)] with s hs hs0
  exact hstrict s hs0 hs

namespace MomentEndpoint
open Classical FiniteTesting FiniteIID EventCounts MomentTesting FiniteAllocationUpper
variable {Ω : Type*} [Fintype Ω]

/-- Reject outside the designated support; randomize with rejection 1/3 inside. -/
def supportTest (S : Finset Ω) (n : ℕ) : FiniteTesting.RandomizedTest (Fin n → Ω) where
  reject x := if ∀ i, x i ∈ S then 1 / 3 else 1
  nonneg x := by split <;> norm_num
  le_one x := by split <;> norm_num

theorem supportTest_acceptance (p : Probability Ω) (S : Finset Ω) (n : ℕ) :
    1 - expectation (productLaw p n) (supportTest S n) =
      (2 / 3 : ℝ) * eventMass p S ^ n := by
  have hprod : mean (productLaw p n)
      (fun x => ∏ i, if x i ∈ S then (1 : ℝ) else 0) = eventMass p S ^ n := by
    rw [mean_productLaw_product p n (fun _ x => if x ∈ S then (1 : ℝ) else 0)]
    simp [mul_ite, eventMass]
  calc
    1 - expectation (productLaw p n) (supportTest S n) =
        ∑ x, (productLaw p n).mass x * (1 - (supportTest S n).reject x) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, (productLaw p n).total,
        expectation]
    _ = (2 / 3 : ℝ) * mean (productLaw p n)
        (fun x => ∏ i, if x i ∈ S then (1 : ℝ) else 0) := by
      rw [mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ∀ i, x i ∈ S
      · simp [supportTest, hx]
        ring
      · simp [supportTest, hx, Finset.prod_boole]
    _ = _ := by rw [hprod]

theorem endpoint_finite_test (q : Probability Ω) {δ : ℝ}
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) (n : ℕ)
    (hn : δ ^ n ≤ (1 : ℝ) / 2) :
    ∃ test : FiniteTesting.RandomizedTest (Fin n → Ω),
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      ∀ p : Probability Ω, 1 - δ < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3 := by
  let S := heavyLabels q δ
  have hfull : eventMass q S = 1 := by
    rw [eventMass, ← q.total]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    rcases hmin i with hz | hδi
    · exact hz
    · exact False.elim (hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hδi⟩))
  refine ⟨supportTest S n, ?_, ?_⟩
  · have h := supportTest_acceptance q S n
    rw [hfull, one_pow] at h
    linarith
  · intro p hp
    have hmass := heavy_eventMass_lt_of_alternative p q hp
    have hpow := pow_le_pow_left₀ (eventMass_nonneg p S) hmass.le n
    rw [supportTest_acceptance]
    nlinarith

end MomentEndpoint

theorem finite_small_overlap_hasIdentityTest_of_pow {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {δ : ℝ}
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) (n : ℕ)
    (hn : δ ^ n ≤ (1 : ℝ) / 2) :
    HasIdentityTest (extendFiniteLaw q) (1 - δ) n := by
  let Q := pooledLaw (extendFiniteLaw q) (Finset.range k)
  have hQ : ∀ i, Q.mass i = 0 ∨ δ ≤ Q.mass i := by
    intro i
    cases i with
    | none => exact Or.inl (FiniteAllocationUpper.finite_pooled_mass_none q)
    | some i =>
        simpa only [Q, FiniteAllocationUpper.finite_pooled_mass_some] using
          (hmin ((FiniteAllocationUpper.rangeIndexEquiv k).symm i))
  obtain ⟨test, hnull, halt⟩ := MomentEndpoint.endpoint_finite_test Q hQ n hn
  apply hasIdentityTest_of_pooled_test (extendFiniteLaw q) (Finset.range k) (1 - δ) n test hnull
  rw [FiniteAllocationUpper.finite_reference_residual_zero, sub_zero]
  exact halt

theorem finite_small_overlap_hasIdentityTest_iff_pow {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) (n : ℕ) :
    HasIdentityTest (extendFiniteLaw q) (1 - δ) n ↔ δ ^ n ≤ (1 : ℝ) / 2 := by
  refine ⟨?_, finite_small_overlap_hasIdentityTest_of_pow q hmin n⟩
  exact zero_label_pow_necessary (extendFiniteLaw q) k
    (extendFiniteLaw_mass_of_not_lt q k (Nat.lt_irrefl k)) hδ0 hδ1 n

theorem small_overlap_pow_threshold_iff_log {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) :
    δ ^ n ≤ (1 : ℝ) / 2 ↔ Real.log 2 / Real.log (1 / δ) ≤ (n : ℝ) := by
  have h := pointMass_pow_threshold_iff_log (ε := 1 - δ)
    (sub_pos.mpr hδ1) (by linarith) n
  simpa only [sub_sub_cancel, one_div, Real.log_inv] using h

theorem finite_small_overlap_hasIdentityTest_iff_exact_count_le {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) (n : ℕ) :
    HasIdentityTest (extendFiniteLaw q) (1 - δ) n ↔
      ⌈Real.log 2 / Real.log (1 / δ)⌉₊ ≤ n := by
  rw [finite_small_overlap_hasIdentityTest_iff_pow q hδ0 hδ1 hmin n,
    small_overlap_pow_threshold_iff_log hδ0 hδ1 n]
  exact Nat.ceil_le.symm

/-- The manuscript's exact endpoint formula, also allowing zero entries in the
finite presentation when the lower mass bound is imposed on positive entries. -/
theorem finite_small_overlap_exact_minimum {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) :
    IsLeast {n : ℕ | HasIdentityTest (extendFiniteLaw q) (1 - δ) n}
      ⌈Real.log 2 / Real.log (1 / δ)⌉₊ := by
  refine ⟨?_, ?_⟩
  · exact (finite_small_overlap_hasIdentityTest_iff_exact_count_le q hδ0 hδ1 hmin _).mpr le_rfl
  · intro n hn
    exact (finite_small_overlap_hasIdentityTest_iff_exact_count_le q hδ0 hδ1 hmin n).mp hn

theorem finite_small_overlap_one_sample_iff {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmin : ∀ i, q.mass i = 0 ∨ δ ≤ q.mass i) :
    HasIdentityTest (extendFiniteLaw q) (1 - δ) 1 ↔ δ ≤ (1 : ℝ) / 2 := by
  simpa only [pow_one] using finite_small_overlap_hasIdentityTest_iff_pow q hδ0 hδ1 hmin 1

/-- With at least two listed positive atoms, the exact endpoint uses one sample. -/
theorem finite_positive_small_overlap_one_sample_minimum {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (hk : 2 ≤ k) {δ : ℝ}
    (hδ0 : 0 < δ) (hmin : ∀ i, δ ≤ q.mass i) :
    IsLeast {n : ℕ | HasIdentityTest (extendFiniteLaw q) (1 - δ) n} 1 := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have hval := congrArg Fin.val h; norm_num [i, j] at hval
  have hsum : q.mass i + q.mass j ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset (Fin k)))
      (fun a _ _ => q.nonneg a)
    simpa only [Finset.sum_pair hij, q.total] using h
  have hδhalf : δ ≤ (1 : ℝ) / 2 := by linarith [hmin i, hmin j]
  have hδ1 : δ < 1 := by linarith
  refine ⟨?_, ?_⟩
  · exact (finite_small_overlap_one_sample_iff q hδ0 hδ1 (fun a => Or.inr (hmin a))).mpr hδhalf
  · intro n hn
    exact successful_test_uses_positive_samples (extendFiniteLaw q) (1 - δ) (by linarith) n hn

theorem finite_positive_small_overlap_log_ceiling_eq_one {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (hk : 2 ≤ k) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hmin : ∀ i, δ ≤ q.mass i) :
    ⌈Real.log 2 / Real.log (1 / δ)⌉₊ = 1 :=
  (finite_small_overlap_exact_minimum q hδ0 hδ1 (fun i => Or.inr (hmin i))).unique
    (finite_positive_small_overlap_one_sample_minimum q hk hδ0 hmin)

end IdentityTesting
