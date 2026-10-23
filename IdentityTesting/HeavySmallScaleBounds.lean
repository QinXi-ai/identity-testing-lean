import IdentityTesting.FiniteProductTV
import IdentityTesting.HeavyTilt

/-! The manuscript's small-count tilt and large-count rounding constants. -/
noncomputable section
namespace IdentityTesting.HeavyTilt
open FiniteTesting HeavySignedFamily HeavyLowerGeometry DominantTilt EmpiricalSeeds

theorem small_heavy_tilt_sample_bound {k : ℕ}
    (q : Probability (Fin (k + 1)))
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4) {T ε : ℝ}
    (hTR : T * tailTotal q < (100000000 : ℝ)) (hε : ε < 2 * tailTotal q)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ∃ ν : Probability (Fin (k + 1)),
      ν.mass 0 = 1 - 3 * tailTotal q ∧
      (∀ i : Fin k, ν.mass i.succ = 3 * q.mass i.succ) ∧
      FiniteTesting.totalVariation ν q = 2 * tailTotal q ∧
      ε < FiniteTesting.totalVariation ν q ∧
      FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) < 1 / 50 := by
  let R := tailTotal q
  have ht := reference_head_tail q
  change q.mass 0 + R = 1 at ht
  have hh : q.mass 0 < 1 := by linarith
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by change R ≤ 1 / 4 at hR; linarith
  have hσ0 : 0 ≤ 2 * R := by positivity
  have hσh : 2 * R ≤ q.mass 0 := by change R ≤ 1 / 4 at hR; linarith
  let ν := tiltLaw q 0 (2 * R) hh hσ0 hσh
  have hνTV : FiniteTesting.totalVariation ν q = 2 * R := by
    have h := tiltLaw_overlap q 0 (2 * R) hh hσ0 hσh Finset.univ (Finset.mem_univ 0)
    rw [q.total] at h
    rw [finite_totalVariation_eq_one_sub_overlap]
    linarith only [h]
  have hf : tiltFactor (q.mass 0) (2 * R) = 3 := by
    unfold tiltFactor
    rw [show 1 - q.mass 0 = R by linarith]
    field_simp [show R ≠ 0 from ne_of_gt hR0]
    <;> ring
  refine ⟨ν, ?_, ?_, hνTV, ?_, ?_⟩
  · change tiltMass q 0 (2 * R) 0 = 1 - 3 * R
    rw [tiltMass_self]
    linarith only [ht]
  · intro i
    change tiltMass q 0 (2 * R) i.succ = 3 * q.mass i.succ
    rw [tiltMass_ne q 0 (2 * R) (Fin.succ_ne_zero i), hf]
  · simpa only [hνTV] using hε
  · have h := totalVariation_productLaw_le ν q n
    rw [hνTV] at h
    have hnr := mul_le_mul_of_nonneg_right hn hR0.le
    change T * R < 100000000 at hTR
    change (n : ℝ) * R ≤ (1 / (10 : ℝ) ^ 10) * T * R at hnr
    nlinarith only [h, hnr, hTR]

theorem large_count_rounding_constants {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hTR : 100000000 ≤ T * R) :
    Real.sqrt (R / T) / R ≤ 1 / 10000 ∧
    32 / T ≤ (32 / 10000) * Real.sqrt (R / T) := by
  obtain ⟨_, hgR, hTg⟩ := large_scale_bounds hR hT hTR
  constructor
  · apply (div_le_iff₀ hR).2
    linarith only [hgR]
  · apply (div_le_iff₀ hT).2
    nlinarith only [hTg]

end IdentityTesting.HeavyTilt
