import IdentityTesting.EffectiveMassAccess

/-! Certified rational value intervals for the original infinite allocation
functional, and effective access to the original (untruncated) total mass. -/
open scoped BigOperators
open Filter Topology
namespace IdentityTesting.RationalComputation

def countableAllocationOracle {a : ℕ → ℝ} (A : EffectiveMassAccess a)
    (t σ : ℚ) (hσ : 0 < σ) : ℚ × ℚ :=
  let b := A.finiteApprox (σ / 4) (by positivity)
  let I := allocationOracle b t (σ / 2)
  (I.1 - σ / 4, I.2 + σ / 4)

theorem countableAllocationOracle_spec {a : ℕ → ℝ} (A : EffectiveMassAccess a)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (t σ : ℚ) (ht : 0 < t) (hσ : 0 < σ) :
    OracleIntervalValid (allocationD a (t : ℝ)) σ (countableAllocationOracle A t σ hσ) := by
  let b := A.finiteApprox (σ / 4) (by positivity)
  have hb := A.finiteApprox_pos (σ / 4) (by positivity)
  have hbR : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast (hb i).le
  have hbs := (extendFiniteVector_hasSum (fun i => (b i : ℝ))).summable
  have hI := allocationOracle_spec b t (σ / 2) hb ht (half_pos hσ)
  have hE := (allocationD_abs_sub_le_l1 (t : ℝ) ha
    (extendFiniteVector_nonneg hbR) hs hbs).trans
      (A.finiteApprox_l1 ha hs (σ / 4) (by positivity))
  have hE' : |allocationD a (t : ℝ) -
      allocationD (extendFiniteVector (fun i => (b i : ℝ))) (t : ℝ)| ≤ (σ : ℝ) / 4 := by
    simpa only [b, Rat.cast_div, Rat.cast_ofNat] using hE
  rcases hI with ⟨hl, hu, hw⟩
  simp only [OracleIntervalValid, countableAllocationOracle, Rat.cast_sub,
    Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  change ((allocationOracle b t (σ / 2)).1 : ℝ) - (σ : ℝ) / 4 ≤ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp hE').1]
  · linarith [(abs_le.mp hE').2]
  · dsimp only [b]
    linarith

theorem accessError_tendsto : Tendsto (fun n => (accessError n : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  simpa only [accessError, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat,
    div_pow, one_pow] using h

theorem EffectiveRealAccess.tendsto {x : ℝ} (X : EffectiveRealAccess x) :
    Tendsto (fun n => (X.approx n : ℝ)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ accessError_tendsto
  intro n
  simpa only [Real.norm_eq_abs] using X.error_le n

theorem EffectiveMassAccess.totalApprox_error {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (n : ℕ) :
    |((∑ i, A.finiteApprox (accessError n) (accessError_pos n) i : ℚ) : ℝ) -
      ∑' i, a i| ≤ (accessError n : ℝ) := by
  let b := fun i => (A.finiteApprox (accessError n) (accessError_pos n) i : ℝ)
  have hb := extendFiniteVector_hasSum b
  have hnorm : Summable (fun i => ‖a i - extendFiniteVector b i‖) := by
    simpa only [Real.norm_eq_abs] using (hs.sub hb.summable).abs
  have h := norm_tsum_le_tsum_norm hnorm
  rw [hs.tsum_sub hb.summable, hb.tsum_eq] at h
  have h' : |(∑' i, a i) - ∑ i, b i| ≤ ∑' i, |a i - extendFiniteVector b i| := by
    simpa only [Real.norm_eq_abs] using h
  rw [abs_sub_comm] at h'
  push_cast
  exact h'.trans (A.finiteApprox_l1 ha hs (accessError n) (accessError_pos n))

/-- The returned approximation covers the full original mass, not just the
prefix mass used internally by a particular finite call. -/
def EffectiveMassAccess.totalAccess {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    EffectiveRealAccess (∑' i, a i) where
  approx n := ∑ i, A.finiteApprox (accessError n) (accessError_pos n) i
  error_le := A.totalApprox_error ha hs

structure EffectiveFunctionAccess (f : ℝ → ℝ) where
  interval : ℚ → ℕ → ℚ × ℚ
  valid : ∀ (t : ℚ) (n : ℕ), 0 < t →
    OracleIntervalValid (f (t : ℝ)) (accessError n) (interval t n)

def countableAllocationAccess {a : ℕ → ℝ} (A : EffectiveMassAccess a)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) : EffectiveFunctionAccess (allocationD a) where
  interval t n := countableAllocationOracle A t (accessError n) (accessError_pos n)
  valid t n ht := countableAllocationOracle_spec A ha hs t (accessError n) ht (accessError_pos n)

end IdentityTesting.RationalComputation
