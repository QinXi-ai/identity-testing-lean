import IdentityTesting.MomentUpperBound

/-! The manuscript's explicit errors for the actual light-label moment tests. -/
noncomputable section
namespace IdentityTesting.MomentTesting
open scoped BigOperators
open Classical FiniteTesting FiniteAllocationUpper EventCounts CollisionTesting
variable {Ω : Type*} [Fintype Ω]

theorem moment_light_sample_geometry (q : Probability Ω) {δ : ℝ} (hδ : 0 < δ)
    (hregime : 1000000000000 * δ < finiteOverlapMoment q δ)
    (hv : eventMass q (heavyLabels q δ) < finiteOverlapMoment q δ / 2) :
    let W := finiteOverlapMoment q δ
    let A := weightedMass q q (lightLabels q δ)
    let B := collisionMass2 q (lightLabels q δ)
    let n := ⌈10000 / W⌉₊
    2 ≤ n ∧ 0 < A ∧ 5000 * Real.sqrt δ < (n : ℝ) * A ∧
      (n : ℝ) ^ 2 * B / 2 < 51 / 1000000 ∧
      4 * Real.sqrt δ * δ ≤ A ∧
      25000000 * δ ≤ (n : ℝ) ^ 2 * A ^ 2 := by
  dsimp only
  let W := finiteOverlapMoment q δ
  let A := weightedMass q q (lightLabels q δ)
  let B := collisionMass2 q (lightLabels q δ)
  let v := eventMass q (heavyLabels q δ)
  let n := ⌈10000 / W⌉₊
  have hW : 0 < W := finiteOverlapMoment_pos q hδ
  have hW1 : W ≤ 1 := finiteOverlapMoment_le_one q δ
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hdecomp : W = v + A / Real.sqrt δ := moment_decomposition q hδ
  have hAeq : A = (W - v) * Real.sqrt δ := (div_eq_iff hs.ne').mp (by linarith)
  have hA0 : 0 < A := by rw [hAeq]; exact mul_pos (by change v < W / 2 at hv; linarith) hs
  have hAlower : Real.sqrt δ * W / 2 ≤ A := by
    rw [hAeq]
    have h := mul_le_mul_of_nonneg_right hv.le hs.le
    change v * Real.sqrt δ ≤ W / 2 * Real.sqrt δ at h
    nlinarith only [h]
  have hAupper : A ≤ Real.sqrt δ * W := by
    rw [hAeq]
    have h := mul_nonneg (eventMass_nonneg q (heavyLabels q δ)) hs.le
    change 0 ≤ v * Real.sqrt δ at h
    nlinarith only [h]
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hBW : B ≤ δ * W := by
    have h := (light_collision_le (q := q) (δ := δ)).trans
      (mul_le_mul_of_nonneg_left hAupper hs.le)
    simpa only [← mul_assoc, Real.mul_self_sqrt hδ.le] using h
  obtain ⟨hn2, _, _, _, hsmall, _⟩ :=
    moment_sample_bounds hδ hW hW1 hregime hAlower hB0 hBW
  obtain ⟨hnW, hnW1⟩ := ceil_ratio_bounds (a := 10000) (by norm_num) hW hW1
  change 10000 ≤ (n : ℝ) * W at hnW
  change (n : ℝ) * W ≤ 10000 + 1 at hnW1
  have hNA : 5000 * Real.sqrt δ < (n : ℝ) * A := by
    have hAstrict : Real.sqrt δ * W / 2 < A := by
      rw [hAeq]
      have h := mul_lt_mul_of_pos_right hv hs
      change v * Real.sqrt δ < W / 2 * Real.sqrt δ at h
      nlinarith only [h]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h1 := mul_lt_mul_of_pos_left hAstrict hnpos
    have h2 := mul_le_mul_of_nonneg_left hnW hs.le
    nlinarith only [h1, h2]
  have hcollision : (n : ℝ) ^ 2 * B / 2 < 51 / 1000000 := by
    have hnWsq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hW.le) hnW1 2
    have hr : B / W ^ 2 ≤ (1 : ℝ) / 1000000000000 := by
      apply (div_le_iff₀ (sq_pos_of_pos hW)).2
      have h := mul_le_mul_of_nonneg_right hregime.le hW.le
      nlinarith only [h, hBW]
    have h := mul_le_mul hnWsq hr (div_nonneg hB0 (sq_nonneg W)) (by norm_num : (0 : ℝ) ≤ (10000 + 1) ^ 2)
    have heq : ((n : ℝ) * W) ^ 2 * (B / W ^ 2) = (n : ℝ) ^ 2 * B := by field_simp
    rw [heq] at h
    nlinarith only [h]
  have hsignal : 25000000 * δ ≤ (n : ℝ) ^ 2 * A ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 5000 * Real.sqrt δ) hNA.le 2
    nlinarith only [h, Real.sq_sqrt hδ.le]
  exact ⟨hn2, hA0, hNA, hcollision, hsmall, hsignal⟩

theorem moment_repeat_miss_sharp (p : Probability Ω) (L : Finset Ω) (n : ℕ)
    (hn : 2 ≤ n) (hsignal : 1562500 ≤ (n : ℝ) ^ 2 * collisionMass2 p L) :
    1 - expectation (productLaw p n) (repeatTest L n) ≤ 256 / (10000 : ℝ) ^ 2 + 128 / 10000 ∧
    1 - expectation (productLaw p n) (repeatTest L n) < 13 / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < collisionMass2 p L := by
    by_contra h
    have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (n : ℝ)) (le_of_not_gt h)
    linarith
  have hden : 1250 ≤ (n : ℝ) * Real.sqrt (collisionMass2 p L) := by
    have heq : ((n : ℝ) * Real.sqrt (collisionMass2 p L)) ^ 2 = (n : ℝ) ^ 2 * collisionMass2 p L := by
      rw [mul_pow, Real.sq_sqrt hp.le]
    nlinarith [mul_nonneg hnR.le (Real.sqrt_nonneg (collisionMass2 p L))]
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (by norm_num) hsignal
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 16) (by norm_num) hden
  have h := (no_repeat_probability_le p L n hn hp).trans (add_le_add h1 h2)
  constructor <;> linarith

theorem moment_actual_error_constants (q : Probability Ω) {δ : ℝ} (hδ : 0 < δ)
    (hregime : 1000000000000 * δ < finiteOverlapMoment q δ)
    (hv : eventMass q (heavyLabels q δ) < finiteOverlapMoment q δ / 2) :
    let L := lightLabels q δ
    let n := ⌈10000 / finiteOverlapMoment q δ⌉₊
    expectation (productLaw q n) (weightedMeanTest q L n) < 32 / 10000 ∧
    expectation (productLaw q n) (repeatTest L n) < 51 / 1000000 ∧
    (∀ p : Probability Ω, weightedMass p q L ≤ weightedMass q q L / 2 →
      1 - expectation (productLaw p n) (weightedMeanTest q L n) < 16 / 10000) ∧
    (∀ p : Probability Ω, 1 - δ < FiniteTesting.totalVariation p q →
      weightedMass q q L / 2 < weightedMass p q L →
      1 - expectation (productLaw p n) (repeatTest L n) < 13 / 1000) := by
  dsimp only
  let L := lightLabels q δ
  let n := ⌈10000 / finiteOverlapMoment q δ⌉₊
  let A := weightedMass q q L
  obtain ⟨hn2, hA, hNA, hcollision, hsmall, hsignal⟩ := moment_light_sample_geometry q hδ hregime hv
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ Real.sqrt δ :=
    fun i hi => Real.sqrt_le_sqrt (light_mass_lt q δ hi).le
  have h16 : 16 * Real.sqrt δ / ((n : ℝ) * A) < 32 / 10000 := by
    apply (div_lt_iff₀ (mul_pos hnR hA)).2
    linarith only [hNA]
  have h8 : 8 * Real.sqrt δ / ((n : ℝ) * A) < 16 / 10000 := by
    apply (div_lt_iff₀ (mul_pos hnR hA)).2
    linarith only [hNA]
  refine ⟨(weightedMeanTest_null_error q L n (Real.sqrt δ) hn0 hA hw).trans_lt h16, ?_, ?_, ?_⟩
  · have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
      rw [Nat.cast_choose_two]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h := mul_le_mul_of_nonneg_right hchoose
      (Finset.sum_nonneg (fun i (_ : i ∈ L) => sq_nonneg (q.mass i)))
    have hr := repeat_probability_le q L n
    change expectation _ _ ≤ _ * collisionMass2 q L at hr
    change _ * collisionMass2 q L ≤ (n : ℝ) ^ 2 / 2 * collisionMass2 q L at h
    nlinarith only [hr, h, hcollision]
  · intro p hsep
    exact (weightedMeanTest_alternative_error p q L n (Real.sqrt δ) hn0 hA
      (Real.sqrt_nonneg δ) hw hsep).trans_lt h8
  · intro p hp hmean
    have hover : localOverlap p q L ≤ 2 * (δ / 2) := by
      have h := localOverlap_le_global p q L
      linarith
    have hs := collision_signal_of_small_overlap p q L (Real.sqrt δ) (δ / 2)
      (Real.sqrt_nonneg δ) (by positivity) hA hw (by nlinarith only [hsmall]) hover hmean
    have hs' := (div_le_iff₀ (by positivity : 0 < 32 * (δ / 2))).1 hs
    have hscaled := mul_le_mul_of_nonneg_left hs' (sq_nonneg (n : ℝ))
    have hprod : 1562500 * δ ≤ (n : ℝ) ^ 2 * collisionMass2 p L * δ := by
      nlinarith only [hsignal, hscaled]
    have hsig : 1562500 ≤ (n : ℝ) ^ 2 * collisionMass2 p L := (mul_le_mul_iff_left₀ hδ).1 hprod
    exact (moment_repeat_miss_sharp p L n hn2 hsig).2

end IdentityTesting.MomentTesting
