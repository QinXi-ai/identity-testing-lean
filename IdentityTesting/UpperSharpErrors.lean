import IdentityTesting.UpperSharpGeometry
import IdentityTesting.FiniteAllocationUpperParameters
import IdentityTesting.FiniteAllocationUpperOverlap

/-! Original numerical error bounds for the actual weighted-mean and collision tests. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID CollisionTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem repeatTest_miss_sharp (p : Probability Ω) (L : Finset Ω) (n : ℕ)
    (hn : 2 ≤ n) (hsignal : (10000 : ℝ) ^ 2 ≤ 12 * (n : ℝ) ^ 2 * collisionMass2 p L) :
    1 - expectation (productLaw p n) (repeatTest L n) ≤
      48 / (10000 : ℝ) ^ 2 + 16 * Real.sqrt 12 / 10000 ∧
    1 - expectation (productLaw p n) (repeatTest L n) < 6 / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < collisionMass2 p L := by
    by_contra h
    have hle := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 12 * (n : ℝ) ^ 2) hle
    nlinarith only [hsignal, hm]
  have hd : 0 < (n : ℝ) * Real.sqrt (collisionMass2 p L) := by positivity
  have hs := Real.sq_sqrt hp.le
  have h12 : Real.sqrt (12 : ℝ) ^ 2 = 12 := Real.sq_sqrt (by norm_num)
  have hprod : 10000 ≤ (n : ℝ) * Real.sqrt (collisionMass2 p L) * Real.sqrt 12 := by
    have he : ((n : ℝ) * Real.sqrt (collisionMass2 p L) * Real.sqrt 12) ^ 2 =
        12 * (n : ℝ) ^ 2 * collisionMass2 p L := by rw [mul_pow, mul_pow, hs, h12]; ring
    nlinarith [mul_nonneg hd.le (Real.sqrt_nonneg (12 : ℝ))]
  have hfirst : 4 / ((n : ℝ) ^ 2 * collisionMass2 p L) ≤ 48 / (10000 : ℝ) ^ 2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hsignal]
  have hsecond : 16 / ((n : ℝ) * Real.sqrt (collisionMass2 p L)) ≤
      16 * Real.sqrt 12 / 10000 := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hprod]
  have he := (no_repeat_probability_le p L n hn hp).trans (add_le_add hfirst hsecond)
  have hs12 : Real.sqrt (12 : ℝ) < 7 / 2 := by nlinarith [Real.sqrt_nonneg (12 : ℝ)]
  exact ⟨he, lt_of_le_of_lt he (by nlinarith only [hs12])⟩

theorem concentrated_actual_error_constants (q : Probability Ω) (x : Ω → ℝ) (T β ε : ℝ)
    (hT : 1 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, q.mass i * x i) = ε)
    (hmax : ∀ i, q.mass i ≤ 2 * (1 - ε))
    (hD : coarseDisplacement q x upperEta ≤ 2 * concentratedResidual q x upperEta) :
    let L := concentratedLabels x upperEta
    let E := concentratedResidual q x upperEta
    let m := ⌈10000 * T⌉₊
    expectation (productLaw q m) (weightedMeanTest q L m) ≤ 576 / 10000 ∧
    (∀ p : Probability Ω, weightedMass p q L ≤ weightedMass q q L / 2 →
      1 - expectation (productLaw p m) (weightedMeanTest q L m) ≤ 288 / 10000) ∧
    expectation (productLaw q m) (repeatTest L m) < 15 / 10000000 ∧
    (∀ p : Probability Ω, (∑ i ∈ L, min (p.mass i) (q.mass i)) < 2 * E →
      weightedMass q q L / 2 < weightedMass p q L →
      1 - expectation (productLaw p m) (repeatTest L m) < 6 / 1000) := by
  dsimp only
  let L := concentratedLabels x upperEta
  let E := concentratedResidual q x upperEta
  let A := weightedMass q q L
  let m := ⌈10000 * T⌉₊
  obtain ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hnull, hsignal, hwratio, hTq2⟩ :=
    concentrated_actual_parameters_with_geometry q x T β ε (by linarith) hβ hx hkkt hbudget hradius hmax hD
  change 2 ≤ m at hm2
  change T ^ 2 * collisionMass2 q L ≤ 288 * upperEta at hTq2
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm : 10000 * T ≤ (m : ℝ) := Nat.le_ceil _
  have hma := mul_le_mul_of_nonneg_right hm hA.le
  have hmean16 : 16 * w / ((m : ℝ) * A) ≤ 576 / 10000 := by
    apply (div_le_iff₀ (mul_pos hmR hA)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ T) hA.le]
  have hmean8 : 8 * w / ((m : ℝ) * A) ≤ 288 / 10000 := by
    apply (div_le_iff₀ (mul_pos hmR hA)).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ T) hA.le]
  refine ⟨(weightedMeanTest_null_error q L m w hm0 hA hw).trans hmean16, ?_, ?_, ?_⟩
  · intro p hsep
    exact (weightedMeanTest_alternative_error p q L m w hm0 hA hw0 hw hsep).trans hmean8
  · have hmupper : (m : ℝ) ≤ 10001 * T := by
      have hc := Nat.ceil_lt_add_one (show 0 ≤ 10000 * T by positivity)
      change (m : ℝ) < 10000 * T + 1 at hc
      linarith
    have hchoose : (m.choose 2 : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
      rw [Nat.cast_choose_two]
      nlinarith [show (0 : ℝ) ≤ m by positivity]
    have hc0 : 0 ≤ collisionMass2 q L := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hc := mul_le_mul_of_nonneg_right hchoose hc0
    have hms := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg m) hmupper 2) hc0
    have ht := mul_le_mul_of_nonneg_left hTq2 (by norm_num : (0 : ℝ) ≤ 10001 ^ 2)
    have hr := repeat_probability_le q L m
    change expectation _ _ ≤ _ * collisionMass2 q L at hr
    norm_num [upperEta] at ht
    nlinarith only [hr, hc, hms, ht]
  · intro p hover hsep
    have hc := collision_signal_of_small_overlap p q L w E hw0 hE hA hw hsmall hover.le hsep
    have hc' := (div_le_iff₀ (by positivity : 0 < 32 * E)).mp hc
    have hscaled := mul_le_mul_of_nonneg_left hc' (sq_nonneg (m : ℝ))
    have hmoment := (concentrated_moment_scale_sharp q x upperEta T β
      (by norm_num [upperEta]) hβ.le hx hkkt hbudget hD).1
    change (8 : ℝ) / 3 * E ≤ T ^ 2 * A ^ 2 at hmoment
    have hms := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity : 0 ≤ 10000 * T) hm 2) (sq_nonneg A)
    have ht := mul_le_mul_of_nonneg_left hmoment (by norm_num : (0 : ℝ) ≤ 100000000)
    have hsig : (10000 : ℝ) ^ 2 ≤ 12 * (m : ℝ) ^ 2 * collisionMass2 p L := by
      have hcombined : E * (100000000 - 12 * (m : ℝ) ^ 2 * collisionMass2 p L) ≤ 0 := by
        nlinarith only [hscaled, hms, ht]
      have : 100000000 - 12 * (m : ℝ) ^ 2 * collisionMass2 p L ≤ 0 :=
        (mul_le_mul_iff_left₀ hE).mp (by simpa only [mul_zero, zero_mul, mul_comm] using hcombined)
      linarith
    exact (repeatTest_miss_sharp p L m hm2 hsig).2

end IdentityTesting.FiniteAllocationUpper

