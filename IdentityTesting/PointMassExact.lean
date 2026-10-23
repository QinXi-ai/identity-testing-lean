import IdentityTesting.DegenerateBranches
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-! The exact point-reference sample complexity in the original countable
observation model. Necessity uses actual two-point alternatives at every
strictly larger radius and takes their radius down to the boundary. -/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

theorem pointMass_hasIdentityTest_of_pow_le_half (j : ℕ) {ε : ℝ}
    (n : ℕ) (hn : (1 - ε) ^ n ≤ (1 : ℝ) / 2) :
    HasIdentityTest (pointMass j) ε n := by
  refine ⟨pointMassTest j n, (pointMassTest_null_error j n).le, ?_⟩
  intro p hp
  rw [totalVariation_to_pointMass] at hp
  have hmass : p.mass j ≤ 1 - ε := by linarith
  have hpow := pow_le_pow_left₀ (p.nonneg j) hmass n
  rw [pointMassTest_acceptance]
  nlinarith

theorem pointMass_pow_le_half_of_hasIdentityTest (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (ht : HasIdentityTest (pointMass j) ε n) :
    (1 - ε) ^ n ≤ (1 : ℝ) / 2 := by
  obtain ⟨test, hnull, halt⟩ := ht
  rw [rejectionProbability_pointMass] at hnull
  have hstrict (s : ℝ) (hes : ε < s) (hs1 : s ≤ 1) :
      (1 - s) ^ n ≤ (1 : ℝ) / 2 := by
    have hs0 : 0 ≤ s := (hε0.trans hes).le
    let p := pointMassAlternative j s hs0 hs1
    have hp : ε < totalVariation p (pointMass j) := by
      rw [pointMassAlternative_distance]
      exact hes
    have haccept := halt p hp
    have hconst := acceptanceProbability_constant_lower_bound p j test
    rw [show p.mass j = 1 - s from pointMassAlternative_mass_self j s hs0 hs1] at hconst
    have hnonneg : 0 ≤ (1 - s) ^ n := pow_nonneg (sub_nonneg.mpr hs1) n
    have hprod := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) / 3 ≤ 1 - test.reject (constantSample j n) by linarith) hnonneg
    nlinarith
  have hlim : Tendsto (fun s : ℝ => (1 - s) ^ n) (𝓝[>] ε) (𝓝 ((1 - ε) ^ n)) :=
    (((continuous_const.sub continuous_id).pow n).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε1)] with s hs hs1
  exact hstrict s hs hs1.le

theorem pointMass_hasIdentityTest_iff_pow_le_half (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    HasIdentityTest (pointMass j) ε n ↔ (1 - ε) ^ n ≤ (1 : ℝ) / 2 :=
  ⟨pointMass_pow_le_half_of_hasIdentityTest j hε0 hε1 n,
    pointMass_hasIdentityTest_of_pow_le_half j n⟩

theorem pointMass_pow_threshold_iff_log {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    (1 - ε) ^ n ≤ (1 : ℝ) / 2 ↔
      Real.log 2 / (-Real.log (1 - ε)) ≤ (n : ℝ) := by
  have hb : 0 < 1 - ε := sub_pos.mpr hε1
  have hblog : Real.log (1 - ε) < 0 := Real.log_neg hb (by linarith)
  have hden : 0 < -Real.log (1 - ε) := neg_pos.mpr hblog
  have hhalf : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [← Real.log_le_log_iff (pow_pos hb n) (by norm_num : (0 : ℝ) < 1 / 2),
    Real.log_pow, hhalf, div_le_iff₀ hden]
  constructor <;> intro h <;> nlinarith only [h]

/-- The exact natural-number formula from the manuscript's point branch. -/
def pointMassExactSampleCount (ε : ℝ) : ℕ :=
  ⌈Real.log 2 / (-Real.log (1 - ε))⌉₊

theorem pointMass_hasIdentityTest_iff_exact_count_le (j : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    HasIdentityTest (pointMass j) ε n ↔ pointMassExactSampleCount ε ≤ n := by
  rw [pointMass_hasIdentityTest_iff_pow_le_half j hε0 hε1 n,
    pointMass_pow_threshold_iff_log hε0 hε1 n]
  exact Nat.ceil_le.symm

theorem point_reference_hasIdentityTest_iff_pow_le_half (q : DiscreteLaw)
    (hq : largestMass q = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    HasIdentityTest q ε n ↔ (1 - ε) ^ n ≤ (1 : ℝ) / 2 := by
  rw [eq_pointMass_of_largestMass_one q hq]
  exact pointMass_hasIdentityTest_iff_pow_le_half _ hε0 hε1 n

theorem point_reference_hasIdentityTest_iff_exact_count_le (q : DiscreteLaw)
    (hq : largestMass q = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ) :
    HasIdentityTest q ε n ↔ pointMassExactSampleCount ε ≤ n := by
  rw [eq_pointMass_of_largestMass_one q hq]
  exact pointMass_hasIdentityTest_iff_exact_count_le _ hε0 hε1 n

/-- The logarithmic ceiling is a successful sample count and is at most every
successful sample count; hence it is the exact minimum in the original model. -/
theorem point_reference_exact_minimum (q : DiscreteLaw) (hq : largestMass q = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    IsLeast {n : ℕ | HasIdentityTest q ε n}
      ⌈Real.log 2 / (-Real.log (1 - ε))⌉₊ := by
  refine ⟨?_, ?_⟩
  · exact (point_reference_hasIdentityTest_iff_exact_count_le q hq hε0 hε1 _).mpr le_rfl
  · intro n hn
    exact (point_reference_hasIdentityTest_iff_exact_count_le q hq hε0 hε1 n).mp hn

end IdentityTesting
