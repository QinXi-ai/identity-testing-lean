import IdentityTesting.EffectiveSqrtAccess

/-! Positive reciprocal access, with a computed positive lower bound. -/
open Filter Topology
namespace IdentityTesting.RationalComputation

theorem EffectiveRealAccess.exists_positive_index {x : ℝ}
    (X : EffectiveRealAccess x) (hx : 0 < x) :
    ∃ n, 2 * accessError n < X.approx n := by
  have hlim : Tendsto (fun n => (X.approx n : ℝ) - 2 * (accessError n : ℝ))
      atTop (𝓝 x) := by
    simpa only [mul_zero, sub_zero] using X.tendsto.sub (accessError_tendsto.const_mul 2)
  obtain ⟨n, hn⟩ := (hlim.eventually_const_lt hx).exists
  exact ⟨n, by exact_mod_cast (show 2 * (accessError n : ℝ) < (X.approx n : ℝ) by linarith)⟩

def EffectiveRealAccess.positiveIndex {x : ℝ} (X : EffectiveRealAccess x) (hx : 0 < x) : ℕ :=
  (certifiedNatSearch _ (X.exists_positive_index hx)).val

def EffectiveRealAccess.positiveLower {x : ℝ} (X : EffectiveRealAccess x) (hx : 0 < x) : ℚ :=
  X.approx (X.positiveIndex hx) - accessError (X.positiveIndex hx)

theorem EffectiveRealAccess.positiveLower_spec {x : ℝ}
    (X : EffectiveRealAccess x) (hx : 0 < x) :
    0 < X.positiveLower hx ∧ (X.positiveLower hx : ℝ) ≤ x := by
  have h := certifiedNatSearch_spec _ (X.exists_positive_index hx)
  change 2 * accessError (X.positiveIndex hx) < X.approx (X.positiveIndex hx) at h
  constructor
  · dsimp only [EffectiveRealAccess.positiveLower]
    linarith [accessError_pos (X.positiveIndex hx)]
  · have he := abs_le.mp (X.error_le (X.positiveIndex hx))
    simp only [EffectiveRealAccess.positiveLower, Rat.cast_sub]
    linarith

def EffectiveRealAccess.invPrecision {x : ℝ} (X : EffectiveRealAccess x)
    (hx : 0 < x) (n : ℕ) : ℕ :=
  oracleDyadicPrecision 1
    (min (X.positiveLower hx / 2) (accessError n * (X.positiveLower hx) ^ 2 / 2))

def EffectiveRealAccess.invApprox {x : ℝ} (X : EffectiveRealAccess x)
    (hx : 0 < x) (n : ℕ) : ℚ := 1 / X.approx (X.invPrecision hx n)

theorem EffectiveRealAccess.invApprox_error {x : ℝ} (X : EffectiveRealAccess x)
    (hx : 0 < x) (n : ℕ) : |(X.invApprox hx n : ℝ) - 1 / x| ≤ (accessError n : ℝ) := by
  let l := X.positiveLower hx
  let m := X.invPrecision hx n
  obtain ⟨hlQ, hlx⟩ := X.positiveLower_spec hx
  have hl : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hlQ
  have hlQ' : (0 : ℚ) < l := hlQ
  have hnQ := accessError_pos n
  have hδQ : 0 < min (l / 2) (accessError n * l ^ 2 / 2) := by positivity
  have hm := oracleDyadicPrecision_spec 1 _ hδQ
  change accessError m ≤ min (l / 2) (accessError n * l ^ 2 / 2) at hm
  have hmR : (accessError m : ℝ) ≤ min ((l : ℝ) / 2)
      ((accessError n : ℝ) * (l : ℝ) ^ 2 / 2) := by
    exact_mod_cast hm
  have he := X.error_le m
  have he1 := abs_le.mp he
  have hlerr := hmR.trans (min_le_left _ _)
  have hnerr := hmR.trans (min_le_right _ _)
  have hym : (l : ℝ) / 2 ≤ (X.approx m : ℝ) := by linarith
  have hy : (0 : ℝ) < (X.approx m : ℝ) := by linarith
  have hden : (l : ℝ) ^ 2 / 2 ≤ (X.approx m : ℝ) * x := by
    have hmul := mul_le_mul hym hlx hl.le hy.le
    nlinarith
  have hn0 : (0 : ℝ) ≤ (accessError n : ℝ) := by exact_mod_cast (accessError_pos n).le
  have hnprod := mul_le_mul_of_nonneg_left hden hn0
  have hid : 1 / (X.approx m : ℝ) - 1 / x =
      (x - (X.approx m : ℝ)) / ((X.approx m : ℝ) * x) := by
    field_simp
    <;> ring
  change |((1 / X.approx m : ℚ) : ℝ) - 1 / x| ≤ _
  rw [Rat.cast_div, Rat.cast_one, hid, abs_div, abs_of_pos (mul_pos hy hx), abs_sub_comm]
  apply (div_le_iff₀ (mul_pos hy hx)).2
  exact he.trans (hnerr.trans (by nlinarith only [hnprod]))

def EffectiveRealAccess.invAccess {x : ℝ} (X : EffectiveRealAccess x) (hx : 0 < x) :
    EffectiveRealAccess (1 / x) where
  approx := X.invApprox hx
  error_le := X.invApprox_error hx

def EffectiveRealAccess.mulRatApprox {x : ℝ} (X : EffectiveRealAccess x)
    (b : ℚ) (n : ℕ) : ℚ := b * X.approx (oracleDyadicPrecision b (accessError n))

theorem EffectiveRealAccess.mulRatApprox_error {x : ℝ} (X : EffectiveRealAccess x)
    (b : ℚ) (hb : 0 ≤ b) (n : ℕ) :
    |(X.mulRatApprox b n : ℝ) - (b : ℝ) * x| ≤ (accessError n : ℝ) := by
  let m := oracleDyadicPrecision b (accessError n)
  have hm := oracleDyadicPrecision_spec b (accessError n) (accessError_pos n)
  have hmR : (b : ℝ) * (accessError m : ℝ) ≤ (accessError n : ℝ) := by
    have h : b * accessError m ≤ accessError n := by
      simpa only [accessError, m, div_eq_mul_inv, one_mul] using hm
    exact_mod_cast h
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  simp only [EffectiveRealAccess.mulRatApprox, Rat.cast_mul, ← mul_sub,
    abs_mul, abs_of_nonneg hbR]
  exact (mul_le_mul_of_nonneg_left (X.error_le m) hbR).trans hmR

def EffectiveRealAccess.mulRatAccess {x : ℝ} (X : EffectiveRealAccess x)
    (b : ℚ) (hb : 0 ≤ b) : EffectiveRealAccess ((b : ℝ) * x) where
  approx := X.mulRatApprox b
  error_le := X.mulRatApprox_error b hb

def EffectiveRealAccess.ratioAccess {δ : ℝ} (D : EffectiveRealAccess δ)
    (hδ : 0 < δ) (b : ℚ) (hb : 0 ≤ b) : EffectiveRealAccess ((b : ℝ) / δ) where
  approx n := b * D.invApprox hδ (oracleDyadicPrecision b (accessError n))
  error_le n := by
    simpa only [mul_one_div] using (D.invAccess hδ).mulRatApprox_error b hb n

end IdentityTesting.RationalComputation
