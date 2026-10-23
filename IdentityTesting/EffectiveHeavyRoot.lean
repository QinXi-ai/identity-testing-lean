import IdentityTesting.EffectiveRootSearch
import IdentityTesting.EffectiveSqrtAccess

/-! Effective heavy roots, retaining a separately certified full count mass.
The original-input wrapper derives this mass from the original vector itself. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def countableHeavyValueIntervalRaw {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (rApprox : ℕ → ℚ) (t : ℚ) (n : ℕ) : ℚ × ℚ :=
  if 0 < t then
    let I := countableAllocationOracle A t (accessError (n + 1)) (accessError_pos _)
    let s := rationalSqrtApprox (fun k =>
      rApprox (oracleDyadicPrecision 1 (accessError k * t)) / t) (n + 3)
    (I.1 + s - accessError (n + 3), I.2 + s + accessError (n + 3))
  else (0, 0)

def countableHeavyValueInterval {a : ℕ → ℝ} {r : ℝ}
    (A : EffectiveMassAccess a) (R : EffectiveRealAccess r) (_hr : 0 ≤ r)
    (t : ℚ) (n : ℕ) : ℚ × ℚ :=
  countableHeavyValueIntervalRaw A R.approx t n

theorem countableHeavyValueInterval_spec {a : ℕ → ℝ} {r : ℝ}
    (A : EffectiveMassAccess a) (R : EffectiveRealAccess r) (hr : 0 ≤ r)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (t : ℚ) (ht : 0 < t) (n : ℕ) :
    OracleIntervalValid (generalHeavyAllocationFunction a r t) (accessError n)
      (countableHeavyValueInterval A R hr t n) := by
  let I := countableAllocationOracle A t (accessError (n + 1)) (accessError_pos _)
  let S := (R.divRatAccess t ht).sqrtAccess (div_nonneg hr (by exact_mod_cast ht.le))
  obtain ⟨hl, hu, hw⟩ := countableAllocationOracle_spec A ha hs t
    (accessError (n + 1)) ht (accessError_pos _)
  have hS := abs_le.mp (S.error_le (n + 3))
  have herr : accessError (n + 1) + 2 * accessError (n + 3) ≤ accessError n := by
    have h3 : n + 3 = ((n + 1) + 1) + 1 := by omega
    simp only [h3, accessError_succ]
    linarith [accessError_pos n]
  simp only [countableHeavyValueInterval, countableHeavyValueIntervalRaw, if_pos ht, OracleIntervalValid,
    Rat.cast_sub, Rat.cast_add]
  change (I.1 : ℝ) + (S.approx (n + 3) : ℝ) - (accessError (n + 3) : ℝ) ≤
    allocationD a t + Real.sqrt (r / t) ∧
    allocationD a t + Real.sqrt (r / t) ≤
      (I.2 : ℝ) + (S.approx (n + 3) : ℝ) + (accessError (n + 3) : ℝ) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · change I.2 + S.approx (n + 3) + accessError (n + 3) -
      (I.1 + S.approx (n + 3) - accessError (n + 3)) ≤ accessError n
    change I.2 - I.1 ≤ accessError (n + 1) at hw
    linarith

def countableHeavyAccess {a : ℕ → ℝ} {r : ℝ}
    (A : EffectiveMassAccess a) (R : EffectiveRealAccess r) (hr : 0 ≤ r)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    EffectiveFunctionAccess (generalHeavyAllocationFunction a r) where
  interval := countableHeavyValueInterval A R hr
  valid t n ht := countableHeavyValueInterval_spec A R hr ha hs t ht n

def countableFullHeavyAccess {a : ℕ → ℝ} (A : EffectiveMassAccess a)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    EffectiveFunctionAccess (generalHeavyAllocationFunction a (∑' i, a i)) where
  interval := countableHeavyValueIntervalRaw A (fun n =>
    ∑ i, A.finiteApprox (accessError n) (accessError_pos n) i)
  valid t n ht := countableHeavyValueInterval_spec A (A.totalAccess ha hs)
    (tsum_nonneg ha) ha hs t ht n

/-- The count term uses `Σ a`, through the certified total-mass access.
No finite prefix mass is substituted for the original heavy coefficient. -/
def countableHeavyRootInterval {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (hr : 0 < ∑' i, a i) (he : 0 < e)
    (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  effectiveRootInterval (countableFullHeavyAccess A ha hs) E ε hε
    (generalHeavyRoot_spec ha hs hr he).1
    (generalHeavyRoot_spec ha hs hr he).2
    (strictAntiOn_generalHeavyAllocationFunction ha hs hr)

theorem countableHeavyRootInterval_spec {a : ℕ → ℝ} {e : ℝ}
    (A : EffectiveMassAccess a) (E : EffectiveRealAccess e)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (hr : 0 < ∑' i, a i) (he : 0 < e)
    (ε : ℚ) (hε : 0 < ε) :
    let I := countableHeavyRootInterval A E ha hs hr he ε hε
    0 < I.1 ∧ (I.1 : ℝ) < generalHeavyRoot a (∑' i, a i) e ∧
      generalHeavyRoot a (∑' i, a i) e < (I.2 : ℝ) ∧ I.2 - I.1 ≤ ε :=
  effectiveRootInterval_spec _ _ _ _ _ _ _

end IdentityTesting.RationalComputation
