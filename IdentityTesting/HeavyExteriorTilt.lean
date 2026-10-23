import IdentityTesting.HeavyTilt

/-! # Actual head tilt and boundary geometry above the heavy radius -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavyExteriorTilt

open FiniteTesting HeavySignedFamily HeavyLowerGeometry DominantTilt EmpiricalSeeds

variable {k : ℕ}

theorem lowDisplacement_le_quarter_complement
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) :
    lowDisplacement q x ≤ (tailTotal q - highMass q x) / 4 := by
  have hsplit := Finset.sum_add_sum_compl (lowTail x) (fun i => q.mass i.succ)
  have hlow : lowDisplacement q x ≤ (∑ i ∈ lowTail x, q.mass i.succ) / 4 := by
    rw [lowDisplacement, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hxi : x i ≤ (1 : ℝ) / 4 := (Finset.mem_filter.mp hi).2
    have h := mul_le_mul_of_nonneg_left hxi (q.nonneg i.succ)
    linarith only [h]
  change _ + highMass q x = tailTotal q at hsplit
  linarith only [hlow, hsplit]

theorem boundary_geometry (q : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {g : ℝ}
    (hboundary : (∑ i, q.mass i.succ * x i) + g = tailTotal q) :
    tailTotal q - highMass q x ≤ 4 * g / 3 ∧ highSlack q x ≤ g := by
  have hid := radius_identity q x hboundary
  have hd := lowDisplacement_le_quarter_complement q x
  have hE := highSlack_nonneg q x (fun i => (hx i).2)
  have hsplit := Finset.sum_add_sum_compl (lowTail x) (fun i => q.mass i.succ)
  have hmass : 0 ≤ tailTotal q - highMass q x := by
    change _ + highMass q x = tailTotal q at hsplit
    have hl := Finset.sum_nonneg (fun i (_ : i ∈ lowTail x) => q.nonneg i.succ)
    linarith only [hsplit, hl]
  constructor <;> linarith only [hid, hd, hE, hmass]

theorem sample_tv_lt_of_exponent (p q : Probability (Fin (k + 1)))
    (hq : ∀ j, 0 < q.mass j) (n : ℕ)
    (hexponent : (n : ℝ) * FiniteChiSquare.chiSquare p q ≤ 100 / (10 : ℝ) ^ 10) :
    FiniteTesting.totalVariation (productLaw p n) (productLaw q n) < 1 / (10 : ℝ) ^ 4 := by
  have hexp := (Real.exp_le_exp.mpr hexponent).trans (Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 100 / (10 : ℝ) ^ 10) (by norm_num))
  have hchi := chiSquare_productLaw_le_exp p q n
  have hnum : (1 : ℝ) / (1 - 100 / (10 : ℝ) ^ 10) - 1 < 4 / (10 : ℝ) ^ 8 := by norm_num
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four (productLaw p n) (productLaw q n)
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  by_contra hnot
  have hlarge : 1 / (10 : ℝ) ^ 4 ≤ FiniteTesting.totalVariation (productLaw p n) (productLaw q n) := le_of_not_gt hnot
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 4) hlarge
  norm_num at hsq
  nlinarith only [hexp, hchi, hnum, hTV, hsq]

theorem exists_near_exterior_tilt
    (q : Probability (Fin (k + 1))) (hq : ∀ j, 0 < q.mass j)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {T Δ : ℝ} (hT : 0 < T) (hTR : (100000000 : ℝ) ≤ T * tailTotal q)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ tailTotal q / 2) :
    ∃ (ν : Probability (Fin (k + 1))) (f : ℝ), 1 ≤ f ∧ f ≤ 2 ∧
      (∀ i : Fin k, ν.mass i.succ = f * q.mass i.succ) ∧
      (∀ s : Finset (Fin (k + 1)), 0 ∈ s →
        (∑ j ∈ s, min (ν.mass j) (q.mass j)) =
          (∑ j ∈ s, q.mass j) - (Δ + 4 * Real.sqrt (tailTotal q / T))) ∧
      (∀ n : ℕ, (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T →
        (n : ℝ) * Δ ^ 2 / tailTotal q ≤ 1 / (10 : ℝ) ^ 10 →
        FiniteTesting.totalVariation (productLaw ν n) (productLaw q n) < 1 / (10 : ℝ) ^ 4) := by
  let R := tailTotal q
  let g := Real.sqrt (R / T)
  let d := Δ + 4 * g
  obtain ⟨hg, hgR, _⟩ := large_scale_bounds hR0 hT hTR
  have htotal := reference_head_tail q
  have hh : q.mass 0 < 1 := by linarith only [htotal, hR0]
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by linarith only [htotal, hR]
  have hd0 : 0 ≤ d := by dsimp [d, g, R]; positivity
  have hdR : d ≤ R := by
    change g ≤ R / 10000 at hgR
    change Δ ≤ R / 2 at hΔ
    dsimp only [d]
    linarith only [hΔ, hgR, hR0]
  have hdh : d ≤ q.mass 0 := by
    change R ≤ 1 / 4 at hR
    linarith only [hdR, hR, hhead]
  let ν := tiltLaw q 0 d hh hd0 hdh
  have hden : 1 - q.mass 0 = R := by
    change q.mass 0 + R = 1 at htotal
    linarith only [htotal]
  have hf2 : tiltFactor (q.mass 0) d ≤ 2 := by
    unfold tiltFactor
    rw [hden]
    have hquot := (div_le_one hR0).2 hdR
    linarith only [hquot]
  refine ⟨ν, tiltFactor (q.mass 0) d, tiltFactor_ge_one hh hd0, hf2, ?_, ?_, ?_⟩
  · intro i
    exact tiltMass_ne q 0 d (Fin.succ_ne_zero i)
  · intro s hs
    exact tiltLaw_overlap q 0 d hh hd0 hdh s hs
  · intro n hn hnΔ
    apply sample_tv_lt_of_exponent ν q hq n
    rw [tiltLaw_chiSquare q 0 d hh hd0 hdh hq, hden]
    have hg2 : g ^ 2 = R / T := Real.sq_sqrt (div_nonneg hR0.le hT.le)
    have hnT : (n : ℝ) / T ≤ 1 / (10 : ℝ) ^ 10 := by
      apply (div_le_iff₀ hT).2
      exact hn
    have hnG : (n : ℝ) * g ^ 2 / R ≤ 1 / (10 : ℝ) ^ 10 := by
      rw [hg2]
      have hRne : R ≠ 0 := ne_of_gt hR0
      convert hnT using 1; field_simp [hRne]
    have hdsq : d ^ 2 ≤ 2 * Δ ^ 2 + 32 * g ^ 2 := by
      dsimp only [d]
      nlinarith only [sq_nonneg (Δ - 4 * g)]
    have hnsq := mul_le_mul_of_nonneg_left hdsq (Nat.cast_nonneg n)
    have hquot : (n : ℝ) * d ^ 2 / R ≤ 34 / (10 : ℝ) ^ 10 := by
      have h : (n : ℝ) * d ^ 2 / R ≤ 2 * ((n : ℝ) * Δ ^ 2 / R) +
          32 * ((n : ℝ) * g ^ 2 / R) := by
        convert div_le_div_of_nonneg_right hnsq hR0.le using 1; ring
      change (n : ℝ) * Δ ^ 2 / R ≤ _ at hnΔ
      nlinarith only [h, hnΔ, hnG]
    have hrearr : (n : ℝ) * (d ^ 2 / (q.mass 0 * R)) =
        ((n : ℝ) * d ^ 2 / R) / q.mass 0 := by ring
    rw [hrearr]
    apply (div_le_iff₀ (hq 0)).2
    have h := mul_le_mul_of_nonneg_left hhead (by norm_num : (0 : ℝ) ≤ 100 / (10 : ℝ) ^ 10)
    norm_num at hquot h ⊢
    linarith only [hquot, h]

end IdentityTesting.HeavyExteriorTilt
