import IdentityTesting.UpperSharpErrors
import IdentityTesting.HeavyUpperParameters

/-! Original heavy-tail numerical errors for the actual two tests. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteIID FiniteAllocationUpper CollisionTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem heavy_actual_error_constants (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (T β g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4))
    (hcase : coarseDisplacement (tailWeights q a) x upperEta + g <
      2 * concentratedResidual (tailWeights q a) x upperEta) :
    let L := fineLabels a x upperEta
    let E := concentratedResidual (tailWeights q a) x upperEta
    let m := ⌈10000 * T⌉₊
    expectation (productLaw q m) (weightedMeanTest q L m) ≤ 96 * upperEta / 10000 ∧
    (∀ p : Probability Ω, weightedMass p q L ≤ weightedMass q q L / 2 →
      1 - expectation (productLaw p m) (weightedMeanTest q L m) ≤ 48 * upperEta / 10000) ∧
    expectation (productLaw q m) (repeatTest L m) < 15 / 10000000 ∧
    (∀ p : Probability Ω, (∑ i ∈ L, min (p.mass i) (q.mass i)) < 2 * E →
      weightedMass q q L / 2 < weightedMass p q L →
      1 - expectation (productLaw p m) (repeatTest L m) < 6 / 1000) := by
  dsimp only
  let Q := tailWeights q a
  let L := fineLabels a x upperEta
  let E := concentratedResidual Q x upperEta
  let A := weightedMass q q L
  let m := ⌈10000 * T⌉₊
  obtain ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hnull, hsignal, hwratio, hTq2⟩ :=
    heavy_actual_parameters_with_geometry q a x T β g hT hβ hg hTg hx hkkt hbudget hcase
  change 2 ≤ m at hm2
  change T ^ 2 * collisionMass2 q L ≤ 288 * upperEta at hTq2
  change w ≤ 6 * upperEta * T * A at hwratio
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm : 10000 * T ≤ (m : ℝ) := Nat.le_ceil _
  have hma := mul_le_mul_of_nonneg_right hm hA.le
  have hmean16 : 16 * w / ((m : ℝ) * A) ≤ 96 * upperEta / 10000 := by
    apply (div_le_iff₀ (mul_pos hmR hA)).2
    norm_num [upperEta, A, L] at hwratio hma ⊢
    nlinarith only [hma, hwratio]
  have hmean8 : 8 * w / ((m : ℝ) * A) ≤ 48 * upperEta / 10000 := by
    apply (div_le_iff₀ (mul_pos hmR hA)).2
    norm_num [upperEta, A, L] at hwratio hma ⊢
    nlinarith only [hma, hwratio]
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
    have hD : coarseDisplacement Q x upperEta ≤ 2 * E := by
      change coarseDisplacement Q x upperEta + g < 2 * E at hcase
      linarith
    have hmoment := (concentrated_moment_scale_sharp Q x upperEta T β
      (by norm_num [upperEta]) hβ.le hx hkkt hbudget hD).1
    rw [tail_weightedMoment q a (concentratedLabels x upperEta)] at hmoment
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

end IdentityTesting.HeavyUpper

