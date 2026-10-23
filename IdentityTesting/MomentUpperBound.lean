import IdentityTesting.MomentTestingGeometry
import IdentityTesting.MomentTestingScalars

/-! Actual finite fixed-sample moment/count upper tester. -/
noncomputable section
namespace IdentityTesting.MomentTesting
open scoped BigOperators
open Classical FiniteTesting EventCounts FiniteAllocationUpper CollisionTesting
variable {Ω : Type*} [Fintype Ω]

theorem exp_neg_le_third {x : ℝ} (hx : 2 ≤ x) : Real.exp (-x) ≤ (1 : ℝ) / 3 := by
  have he : 3 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  rw [Real.exp_neg, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) he

theorem finite_moment_identity_test_sharp (q : Probability Ω) (δ : ℝ) (hδ : 0 < δ)
    (hv : 2 * δ ≤ eventMass q (heavyLabels q δ)) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)),
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      (∀ p : Probability Ω, 1 - δ < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3) ∧
      (n : ℝ) ≤ 50000000000001 / finiteOverlapMoment q δ := by
  classical
  let W := finiteOverlapMoment q δ
  let H := heavyLabels q δ
  let L := lightLabels q δ
  let v := eventMass q H
  have hW : 0 < W := finiteOverlapMoment_pos q hδ
  have hW1 : W ≤ 1 := finiteOverlapMoment_le_one q δ
  have hv0 : 0 < v := by dsimp only [v, H]; linarith
  have hv1 : v ≤ 1 := eventMass_le_one q H
  by_cases hc : W ≤ 500000000000 * v
  · let n := ⌈100 / v⌉₊
    have hround := ceil_ratio_bounds (a := 100) (by norm_num) hv0 hv1
    have hnV : 100 ≤ (n : ℝ) * v := hround.1
    have hn0 : 0 < n := by
      by_contra hn
      have hz : n = 0 := Nat.eq_zero_of_not_pos hn
      simp only [hz, Nat.cast_zero, zero_mul] at hnV
      norm_num at hnV
    have hnV1 : (n : ℝ) * v ≤ 101 := by
      simpa only [n, show (100 : ℝ) + 1 = 101 by norm_num] using hround.2
    refine ⟨n, lowerCountTest H n v, ?_, ?_, ?_⟩
    · have h := lowerCountTest_null_error q H n hn0
      have he := exp_neg_le_third (x := (n : ℝ) * v / 32) (by linarith)
      have he' : Real.exp (-(n : ℝ) * v / 32) ≤ (1 : ℝ) / 3 := by
        simpa only [neg_div, neg_mul] using he
      exact h.trans he'
    · intro p hp
      have hmass := heavy_eventMass_lt_of_alternative p q hp
      have hsep : eventMass p H ≤ eventMass q H / 2 := by
        dsimp only [H]
        linarith
      have h := lowerCountTest_alternative_error q p H n hn0 hsep
      have he := exp_neg_le_third (x := (n : ℝ) * v / 20) (by linarith)
      have he' : Real.exp (-(n : ℝ) * v / 20) ≤ (1 : ℝ) / 3 := by
        simpa only [neg_div, neg_mul] using he
      exact h.trans he'
    · have hn : (n : ℝ) ≤ 100 / v + 1 :=
        (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 100 / v)).le
      have hratio : 100 / v ≤ 50000000000000 / W :=
        (div_le_div_iff₀ hv0 hW).mpr (by nlinarith only [hc])
      have hone : (1 : ℝ) ≤ 1 / W := (le_div_iff₀ hW).mpr (by simpa using hW1)
      calc
        (n : ℝ) ≤ 50000000000000 / W + 1 := hn.trans (add_le_add_right hratio 1)
        _ ≤ 50000000000000 / W + 1 / W := add_le_add_left hone _
        _ = 50000000000001 / W := by ring
  · let A := weightedMass q q L
    let B := collisionMass2 q L
    have hregime : 1000000000000 * δ < W := by
      have hv' : 2 * δ ≤ v := hv
      linarith
    have hvW : v < W / 2 := by linarith [eventMass_nonneg q H]
    have hdecomp : W = v + A / Real.sqrt δ := moment_decomposition q hδ
    have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    have hAeq : A = (W - v) * Real.sqrt δ :=
      (div_eq_iff hs.ne').mp (by linarith only [hdecomp])
    have hA0 : 0 < A := by rw [hAeq]; exact mul_pos (by linarith) hs
    have hAlower : Real.sqrt δ * W / 2 ≤ A := by
      rw [hAeq]
      have h := mul_le_mul_of_nonneg_right hvW.le hs.le
      nlinarith only [h]
    have hAupper : A ≤ Real.sqrt δ * W := by
      rw [hAeq]
      have h := mul_nonneg (eventMass_nonneg q H) hs.le
      nlinarith only [h]
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hBW : B ≤ δ * W := by
      calc
        B ≤ Real.sqrt δ * A := light_collision_le (q := q) (δ := δ)
        _ ≤ Real.sqrt δ * (Real.sqrt δ * W) := mul_le_mul_of_nonneg_left hAupper hs.le
        _ = δ * W := by rw [← mul_assoc, Real.mul_self_sqrt hδ.le]
    obtain ⟨hn2, hnupper, hmean, hcollision, hsmall, hsignal⟩ :=
      moment_sample_bounds hδ hW hW1 hregime hAlower hB0 hBW
    let n := ⌈10000 / W⌉₊
    have hw : ∀ i ∈ L, Real.sqrt (q.mass i) ≤ Real.sqrt δ :=
      fun i hi => Real.sqrt_le_sqrt (light_mass_lt q δ hi).le
    refine ⟨n, weightedMeanRepeatTest q L n, ?_, ?_, ?_⟩
    · exact (weightedMeanRepeatTest_null_error q L n (Real.sqrt δ)
        (by omega) hA0 hw hmean hcollision).trans (by norm_num)
    · intro p hp
      have hover : localOverlap p q L ≤ 2 * (δ / 2) := by
        have h := localOverlap_le_global p q L
        linarith
      apply (weightedMeanRepeatTest_alternative_error p q L n (Real.sqrt δ) (δ / 2)
        hn2 hs.le (by positivity) hA0 hw hmean ?_ hover ?_).trans (by norm_num)
      · nlinarith only [hsmall]
      · nlinarith only [hsignal]
    · apply hnupper.trans
      exact div_le_div_of_nonneg_right (by norm_num : (10001 : ℝ) ≤ 50000000000001) hW.le

/-- Compatibility interface for the previously used rounded constant. -/
theorem finite_moment_identity_test (q : Probability Ω) (δ : ℝ) (hδ : 0 < δ)
    (hv : 2 * δ ≤ eventMass q (heavyLabels q δ)) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)),
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      (∀ p : Probability Ω, 1 - δ < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3) ∧
      (n : ℝ) ≤ 100000000000000 / finiteOverlapMoment q δ := by
  obtain ⟨n, test, hn, ha, hb⟩ := finite_moment_identity_test_sharp q δ hδ hv
  exact ⟨n, test, hn, ha, hb.trans (div_le_div_of_nonneg_right (by norm_num)
    (finiteOverlapMoment_pos q hδ).le)⟩

end IdentityTesting.MomentTesting
