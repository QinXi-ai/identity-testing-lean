import IdentityTesting.EffectiveAllocationOracle
import IdentityTesting.RationalSqrtInterval

/-! Computable square roots and rational rescaling of effective real inputs. -/
namespace IdentityTesting.RationalComputation

theorem accessError_succ (n : ℕ) : accessError (n + 1) = accessError n / 2 := by
  simp only [accessError, pow_succ]
  ring

theorem accessError_double (n : ℕ) : accessError (2 * n) = (accessError n) ^ 2 := by
  simp only [accessError, Nat.mul_comm 2 n, pow_mul, div_pow, one_pow]

theorem sqrt_abs_sub_le_of_sq_bound {x y ε : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hε : 0 ≤ ε) (h : |x - y| ≤ ε ^ 2) :
    |Real.sqrt x - Real.sqrt y| ≤ ε := by
  have hxy := abs_le.mp h
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have h0x := Real.sqrt_nonneg x
  have h0y := Real.sqrt_nonneg y
  rw [abs_le]
  constructor
  · by_contra hn
    have hd : ε < Real.sqrt y - Real.sqrt x := by linarith
    have hm := mul_nonneg h0x (show 0 ≤ Real.sqrt y - Real.sqrt x by linarith)
    nlinarith
  · by_contra hn
    have hd : ε < Real.sqrt x - Real.sqrt y := by linarith
    have hm := mul_nonneg h0y (show 0 ≤ Real.sqrt x - Real.sqrt y by linarith)
    nlinarith

theorem EffectiveRealAccess.clipped_error {x : ℝ} (X : EffectiveRealAccess x)
    (hx : 0 ≤ x) (n : ℕ) : |(max (X.approx n) 0 : ℚ) - x| ≤ (accessError n : ℝ) := by
  have h := abs_le.mp (X.error_le n)
  simp only [Rat.cast_max, Rat.cast_zero]
  rw [abs_le]
  by_cases hp : (X.approx n : ℝ) ≤ 0
  · rw [max_eq_right hp]
    constructor <;> linarith
  · rw [max_eq_left (le_of_not_ge hp)]
    exact h

def rationalSqrtApprox (approx : ℕ → ℚ) (n : ℕ) : ℚ :=
  (sqrtInterval (max (approx (2 * (n + 1))) 0) (accessError (n + 1))).1

def EffectiveRealAccess.sqrtApprox {x : ℝ} (X : EffectiveRealAccess x) (n : ℕ) : ℚ :=
  rationalSqrtApprox X.approx n

theorem EffectiveRealAccess.sqrtApprox_error {x : ℝ} (X : EffectiveRealAccess x)
    (hx : 0 ≤ x) (n : ℕ) :
    |(X.sqrtApprox n : ℝ) - Real.sqrt x| ≤ (accessError n : ℝ) := by
  let q := max (X.approx (2 * (n + 1))) 0
  have hq : (0 : ℚ) ≤ q := le_max_right _ _
  have he : (0 : ℝ) ≤ (accessError (n + 1) : ℝ) := by
    exact_mod_cast (accessError_pos (n + 1)).le
  have hqerr : |(q : ℝ) - x| ≤ (accessError (n + 1) : ℝ) ^ 2 := by
    have h := X.clipped_error hx (2 * (n + 1))
    rw [accessError_double] at h
    simpa only [q, Rat.cast_pow] using h
  have hsq := sqrt_abs_sub_le_of_sq_bound (by exact_mod_cast hq) hx he hqerr
  obtain ⟨_, hl, hu, hw⟩ := sqrtInterval_spec q (accessError (n + 1)) hq
    (accessError_pos (n + 1))
  have hwR : ((sqrtInterval q (accessError (n + 1))).2 : ℝ) -
      ((sqrtInterval q (accessError (n + 1))).1 : ℝ) ≤ (accessError (n + 1) : ℝ) := by
    exact_mod_cast hw
  have heq : 2 * (accessError (n + 1) : ℝ) = (accessError n : ℝ) := by
    rw [accessError_succ]
    push_cast
    ring
  change |((sqrtInterval q (accessError (n + 1))).1 : ℝ) - Real.sqrt x| ≤ _
  rw [abs_le] at hsq ⊢
  constructor <;> linarith

def EffectiveRealAccess.sqrtAccess {x : ℝ} (X : EffectiveRealAccess x) (hx : 0 ≤ x) :
    EffectiveRealAccess (Real.sqrt x) where
  approx := X.sqrtApprox
  error_le := X.sqrtApprox_error hx

def EffectiveRealAccess.divRatApprox {x : ℝ} (X : EffectiveRealAccess x) (t : ℚ)
    (n : ℕ) : ℚ := X.approx (oracleDyadicPrecision 1 (accessError n * t)) / t

theorem EffectiveRealAccess.divRatApprox_error {x : ℝ} (X : EffectiveRealAccess x)
    (t : ℚ) (ht : 0 < t) (n : ℕ) :
    |(X.divRatApprox t n : ℝ) - x / (t : ℝ)| ≤ (accessError n : ℝ) := by
  let m := oracleDyadicPrecision 1 (accessError n * t)
  have hm := oracleDyadicPrecision_spec 1 (accessError n * t) (mul_pos (accessError_pos n) ht)
  change accessError m ≤ accessError n * t at hm
  have hmR : (accessError m : ℝ) ≤ (accessError n : ℝ) * (t : ℝ) := by
    exact_mod_cast hm
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  simp only [EffectiveRealAccess.divRatApprox, Rat.cast_div, ← sub_div, abs_div,
    abs_of_pos htR]
  apply (div_le_iff₀ htR).2
  exact (X.error_le m).trans hmR

def EffectiveRealAccess.divRatAccess {x : ℝ} (X : EffectiveRealAccess x)
    (t : ℚ) (ht : 0 < t) : EffectiveRealAccess (x / (t : ℝ)) where
  approx := X.divRatApprox t
  error_le := X.divRatApprox_error t ht

end IdentityTesting.RationalComputation
