import IdentityTesting.ProfileTestingWeights
import IdentityTesting.EventCounts

/-! Deterministic transfer of TV separation to the light count or heavy signal. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.ProfileTesting
open FiniteTesting FiniteIID EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

theorem totalVariation_le_tail_discrepancy (p q : Probability Ω) (a : Ω) :
    totalVariation p q ≤ ∑ i ∈ tailLabels a, |p.mass i - q.mass i| := by
  have hsum : (∑ i ∈ tailLabels a, (p.mass i - q.mass i)) = -(p.mass a - q.mass a) := by
    have h := Finset.sum_erase_add Finset.univ (fun i => p.mass i - q.mass i) (Finset.mem_univ a)
    simp only [Finset.sum_sub_distrib, p.total, q.total, sub_self] at h
    dsimp [tailLabels]
    rw [Finset.sum_sub_distrib]
    linarith
  have habs := Finset.abs_sum_le_sum_abs (fun i => p.mass i - q.mass i) (tailLabels a)
  rw [hsum, abs_neg] at habs
  have hsplit := Finset.sum_erase_add Finset.univ (fun i => |p.mass i - q.mass i|) (Finset.mem_univ a)
  unfold totalVariation
  dsimp [tailLabels] at *
  linarith

omit [DecidableEq Ω] in
theorem discrepancy_le_mass_add (p q : Probability Ω) (E : Finset Ω) :
    (∑ i ∈ E, |p.mass i - q.mass i|) ≤ eventMass p E + eventMass q E := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply abs_le.mpr
  constructor <;> linarith [p.nonneg i, q.nonneg i]

theorem profileRadius_floor (q : Probability Ω) (a : Ω) (m : ℕ) :
    1 / (m : ℝ) ≤ profileRadius q a m := by
  unfold profileRadius
  exact le_add_of_nonneg_right (div_nonneg
    (Real.rpow_nonneg (weightSum_nonneg q a) _) (Real.sqrt_nonneg _))

theorem profileRadius_pos (q : Probability Ω) (a : Ω) (m : ℕ) (hm : 0 < m) :
    0 < profileRadius q a m :=
  (one_div_pos.mpr (Nat.cast_pos.mpr hm)).trans_le (profileRadius_floor q a m)

theorem light_reference_mass_le_radius (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) :
    eventMass q (lightLabels q a m) ≤ profileRadius q a m := by
  apply (light_reference_mass_le q a m hm hS).trans
  exact le_add_of_nonneg_left (one_div_nonneg.mpr (Nat.cast_nonneg m))

theorem light_count_threshold_le (q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a) :
    countThreshold m (eventMass q (lightLabels q a m)) 1000 ≤ 2000 * profileRadius q a m := by
  let r := profileRadius q a m
  have hr0 : 0 ≤ r := (profileRadius_pos q a m hm).le
  have hrN : 1 / (m : ℝ) ≤ r := profileRadius_floor q a m
  have hmass : eventMass q (lightLabels q a m) ≤ r := light_reference_mass_le_radius q a m hm hS
  have hsq : eventMass q (lightLabels q a m) / m ≤ r ^ 2 := by
    have h1 := div_le_div_of_nonneg_right hmass (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_left hrN hr0
    exact h1.trans (by simpa only [one_div, div_eq_mul_inv, pow_two, one_mul] using h2)
  have hsqrt : Real.sqrt (eventMass q (lightLabels q a m) / m) ≤ r :=
    Real.sqrt_le_iff.mpr ⟨hr0, hsq⟩
  unfold countThreshold
  dsimp [r] at *
  linarith

theorem light_discrepancy_le_of_not_separated (p q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a)
    (hsmall : |eventMass p (lightLabels q a m) - eventMass q (lightLabels q a m)| <
      2 * countThreshold m (eventMass q (lightLabels q a m)) 1000) :
    (∑ i ∈ lightLabels q a m, |p.mass i - q.mass i|) ≤ 4002 * profileRadius q a m := by
  have hdisc := discrepancy_le_mass_add p q (lightLabels q a m)
  have hmass := light_reference_mass_le_radius q a m hm hS
  have hb := light_count_threshold_le q a m hm hS
  have hd := le_abs_self (eventMass p (lightLabels q a m) - eventMass q (lightLabels q a m))
  linarith

theorem tail_discrepancy_split (p q : Probability Ω) (a : Ω) (m : ℕ) :
    (∑ i ∈ tailLabels a, |p.mass i - q.mass i|) =
      (∑ i ∈ heavyLabels q a m, |p.mass i - q.mass i|) +
        ∑ i ∈ lightLabels q a m, |p.mass i - q.mass i| := by
  have h := Finset.sum_sdiff (heavyLabels_subset q a m) (f := fun i => |p.mass i - q.mass i|)
  dsimp [lightLabels]
  linarith

theorem tail_scale_square (S M : ℝ) (hS : 0 < S) (hM : 0 < M) :
    (S ^ ((3 : ℝ) / 4) / Real.sqrt M) ^ 2 = S * Real.sqrt S / M := by
  rw [← sqrt_cutoff_identity S M hS hM, mul_pow, Real.sq_sqrt (by positivity)]
  have hR : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hsq := Real.sq_sqrt hS.le
  field_simp
  nlinarith

theorem heavy_signal_of_TV (p q : Probability Ω) (a : Ω) (m : ℕ)
    (hm : 0 < m) (hS : 0 < weightSum q a)
    (hTV : 20000 * profileRadius q a m < totalVariation p q)
    (hsmall : |eventMass p (lightLabels q a m) - eventMass q (lightLabels q a m)| <
      2 * countThreshold m (eventMass q (lightLabels q a m)) 1000) :
    100000000 * Real.sqrt (weightSum q a) / m ≤
      weightedSignal p q (heavyLabels q a m) (powerWeight q) := by
  let H := heavyLabels q a m
  let S := weightSum q a
  let d := ∑ i ∈ H, |p.mass i - q.mass i|
  let t := S ^ ((3 : ℝ) / 4) / Real.sqrt m
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have htail := totalVariation_le_tail_discrepancy p q a
  rw [tail_discrepancy_split p q a m] at htail
  have hlight := light_discrepancy_le_of_not_separated p q a m hm hS hsmall
  have hr := profileRadius_pos q a m hm
  have ht : t ≤ profileRadius q a m := le_add_of_nonneg_left (one_div_nonneg.mpr hmR.le)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hd : 10000 * t ≤ d := by dsimp [d, H]; linarith
  have hsq : (10000 * t) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
  have hCS := weighted_discrepancy_sq_le p q H (powerWeight q)
    (fun i hi => heavy_weight_pos q a m hm hS i hi)
  have hE := weightedSignal_nonneg p q H (powerWeight q) (fun i _ => powerWeight_nonneg q i)
  have hsum : (∑ i ∈ H, powerWeight q i) ≤ S :=
    Finset.sum_le_sum_of_subset_of_nonneg (heavyLabels_subset q a m)
      (fun i _ _ => powerWeight_nonneg q i)
  have hscale : t ^ 2 = S * Real.sqrt S / m := tail_scale_square S m hS hmR
  apply (mul_le_mul_iff_right₀ hS).mp
  calc
    S * (100000000 * Real.sqrt S / m) = (10000 * t) ^ 2 := by rw [mul_pow, hscale]; ring
    _ ≤ d ^ 2 := hsq
    _ ≤ weightedSignal p q H (powerWeight q) * ∑ i ∈ H, powerWeight q i := hCS
    _ ≤ weightedSignal p q H (powerWeight q) * S := mul_le_mul_of_nonneg_left hsum hE
    _ = _ := by ring

theorem zero_weightSum_tail_mass (q : Probability Ω) (a : Ω) (hS : weightSum q a = 0) :
    eventMass q (tailLabels a) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hw : powerWeight q i = 0 := le_antisymm (by simpa [hS] using powerWeight_le_sum q a i hi)
    (powerWeight_nonneg q i)
  have h := powerWeight_sqrt q i
  rw [hw, zero_mul] at h
  exact h.symm

end IdentityTesting.ProfileTesting
