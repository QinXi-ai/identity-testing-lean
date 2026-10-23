import IdentityTesting.DominantTilt

/-! The manuscript's square-root sample-TV estimate in its small-exponent regime.
It follows directly from the already proved product chi-square identity. -/
noncomputable section
namespace IdentityTesting.DominantTilt
open FiniteTesting FiniteChiSquare
variable {Ω : Type*} [Fintype Ω]

theorem productLaw_totalVariation_le_sqrt_half (p q : Probability Ω)
    (hq : ∀ i, 0 < q.mass i) (n : ℕ) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    (hchi : (n : ℝ) * chiSquare p q ≤ b) :
    FiniteTesting.totalVariation (productLaw p n) (productLaw q n) ≤ Real.sqrt (b / 2) := by
  have hden : 0 < 1 - b := by linarith
  have hexp := (Real.exp_le_exp.mpr hchi).trans
    (Real.exp_bound_div_one_sub_of_interval hb0 (by linarith))
  have hrecip : 1 / (1 - b) ≤ 1 + 2 * b := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb)]
  have hc := chiSquare_productLaw_le_exp p q n
  have hv := totalVariation_sq_le_chiSquare_div_four (productLaw p n) (productLaw q n)
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ b / 2)
  have hs0 := Real.sqrt_nonneg (b / 2)
  nlinarith only [hexp, hrecip, hc, hv, hs, hs0,
    sq_nonneg (FiniteTesting.totalVariation (productLaw p n) (productLaw q n) - Real.sqrt (b / 2))]

theorem productLaw_totalVariation_le_sqrt_rate (p q : Probability Ω)
    (hq : ∀ i, 0 < q.mass i) {T c : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 160) (hrate : chiSquare p q ≤ 80 / T) (n : ℕ)
    (hn : (n : ℝ) ≤ c * T) :
    FiniteTesting.totalVariation (productLaw p n) (productLaw q n) ≤ Real.sqrt (40 * n / T) ∧
      FiniteTesting.totalVariation (productLaw p n) (productLaw q n) ≤ Real.sqrt (40 * c) := by
  have hquot : (n : ℝ) / T ≤ c := (div_le_iff₀ hT).2 hn
  have hb0 : 0 ≤ 80 * n / T := by positivity
  have hb : 80 * n / T ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 80)
    rw [← mul_div_assoc] at hh
    nlinarith only [hh, hc]
  have hchi : (n : ℝ) * chiSquare p q ≤ 80 * n / T := by
    convert mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg n) using 1 <;> ring
  have h := productLaw_totalVariation_le_sqrt_half p q hq n hb0 hb hchi
  rw [show (80 * (n : ℝ) / T) / 2 = 40 * n / T by ring] at h
  refine ⟨h, h.trans (Real.sqrt_le_sqrt ?_)⟩
  have hh := mul_le_mul_of_nonneg_left hquot (by norm_num : (0 : ℝ) ≤ 40)
  rw [← mul_div_assoc] at hh
  nlinarith only [hh]

variable [DecidableEq Ω]

/-- The deterministic tilt's exact square-root bound in the small-sample regime. -/
theorem tiltLaw_productTV_le_sqrt (q : Probability Ω) (i : Ω) (σ : ℝ)
    (hq : ∀ j, 0 < q.mass j) (hh : q.mass i < 1)
    (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i) (n : ℕ)
    (hsmall : (n : ℝ) * σ ^ 2 / (q.mass i * (1 - q.mass i)) ≤ 1 / 2) :
    FiniteTesting.totalVariation (productLaw (tiltLaw q i σ hh hσ0 hσh) n)
      (productLaw q n) ≤ Real.sqrt ((n : ℝ) * σ ^ 2 / (2 * q.mass i * (1 - q.mass i))) := by
  have hb0 : 0 ≤ (n : ℝ) * σ ^ 2 / (q.mass i * (1 - q.mass i)) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg σ))
      (mul_nonneg (q.nonneg i) (by linarith))
  have hchi : (n : ℝ) * chiSquare (tiltLaw q i σ hh hσ0 hσh) q =
      (n : ℝ) * σ ^ 2 / (q.mass i * (1 - q.mass i)) := by
    rw [tiltLaw_chiSquare q i σ hh hσ0 hσh hq]
    ring
  have h := productLaw_totalVariation_le_sqrt_half _ q hq n hb0 hsmall hchi.le
  convert h using 1
  congr 1
  field_simp
  <;> ring

theorem allocation_tilt_totalVariation_manuscript (q : Probability Ω) (x : Ω → ℝ)
    {T c : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 160)
    (hq : ∀ j, 0 < q.mass j) (hx : ∀ j, 0 ≤ x j ∧ x j < 1)
    (hbudget : T ^ 2 * (∑ j, (q.mass j) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (i : Ω) (σ : ℝ) (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i)
    (hcap : q.mass i ≤ 4 / 5) (hσfour : σ ≤ 4 * q.mass i * x i)
    (n : ℕ) (hn : (n : ℝ) ≤ c * T) :
    FiniteTesting.totalVariation (productLaw (tiltLaw q i σ hh hσ0 hσh) n) (productLaw q n) ≤
      Real.sqrt (40 * n / T) ∧
    FiniteTesting.totalVariation (productLaw (tiltLaw q i σ hh hσ0 hσh) n) (productLaw q n) ≤
      Real.sqrt (40 * c) :=
  productLaw_totalVariation_le_sqrt_rate _ q hq hT hc0 hc
    (tiltLaw_allocation_chiSquare_le q x hT hq hx hbudget i σ hh hσ0 hσh hcap hσfour) n hn

theorem paired_combined_cost_manuscript :
    (1 : ℝ) / 10 ^ 9 + 128000 / 10 ^ 12 + 1 / (2 * 100000) < 1 / 10000 := by norm_num

theorem tilted_combined_cost_manuscript :
    Real.sqrt ((40 : ℝ) / 10 ^ 12) + 384000 / 10 ^ 12 + 9 / (2 * 100000) < 1 / 10000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 40 / 10 ^ 12)
  have hs0 := Real.sqrt_nonneg ((40 : ℝ) / 10 ^ 12)
  have hbound : Real.sqrt ((40 : ℝ) / 10 ^ 12) < 1 / 100000 := by nlinarith
  linarith

end IdentityTesting.DominantTilt
