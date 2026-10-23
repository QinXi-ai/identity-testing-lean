import IdentityTesting.PairedRootLowerBound

/-!
# The actual dominant-displacement tilt

One selected mass is decreased by `σ`, and all other original masses are
multiplied by `1 + σ/(1-h)`. Positivity, normalization, exact chi-square and
overlap are proved for the resulting probability law.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.DominantTilt

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def tiltFactor (h σ : ℝ) : ℝ := 1 + σ / (1 - h)

theorem tiltFactor_ge_one {h σ : ℝ} (hh : h < 1) (hσ : 0 ≤ σ) :
    1 ≤ tiltFactor h σ := by
  have := div_nonneg hσ (sub_nonneg.mpr hh.le)
  unfold tiltFactor
  linarith

theorem tiltFactor_balance {h σ : ℝ} (hh : h < 1) :
    tiltFactor h σ * (1 - h) = 1 - h + σ := by
  unfold tiltFactor
  field_simp [ne_of_gt (sub_pos.mpr hh)]

theorem tiltFactor_le_three {h σ : ℝ} (hh : h ≤ (4 : ℝ) / 5)
    (hσ : σ ≤ h / 2) : tiltFactor h σ ≤ 3 := by
  have hden : 0 < 1 - h := by linarith
  have hquot : σ / (1 - h) ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
  unfold tiltFactor
  linarith

def tiltMass (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ) (j : Ω) : ℝ :=
  if j = i then q.mass i - σ else tiltFactor (q.mass i) σ * q.mass j

@[simp] theorem tiltMass_self (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ) :
    tiltMass q i σ i = q.mass i - σ := by simp [tiltMass]

theorem tiltMass_ne (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ) {j : Ω} (hj : j ≠ i) :
    tiltMass q i σ j = tiltFactor (q.mass i) σ * q.mass j := by simp [tiltMass, hj]

theorem tiltMass_nonneg (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i) (j : Ω) :
    0 ≤ tiltMass q i σ j := by
  by_cases hj : j = i
  · subst j
    simpa only [tiltMass_self] using sub_nonneg.mpr hσh
  · rw [tiltMass_ne q i σ hj]
    exact mul_nonneg (le_trans (by norm_num) (tiltFactor_ge_one hh hσ0)) (q.nonneg j)

theorem sum_reference_erase (q : FiniteTesting.Probability Ω) (i : Ω) :
    (∑ j ∈ Finset.univ.erase i, q.mass j) = 1 - q.mass i := by
  have h := Finset.sum_erase_add Finset.univ q.mass (Finset.mem_univ i)
  rw [q.total] at h
  linarith only [h]

theorem tiltMass_total (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) : ∑ j, tiltMass q i σ j = 1 := by
  have hrest : (∑ j ∈ Finset.univ.erase i, tiltMass q i σ j) =
      tiltFactor (q.mass i) σ * (1 - q.mass i) := by
    rw [← sum_reference_erase q i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact tiltMass_ne q i σ (Finset.mem_erase.mp hj).1
  calc
    _ = (∑ j ∈ Finset.univ.erase i, tiltMass q i σ j) + tiltMass q i σ i :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    _ = 1 := by rw [hrest, tiltMass_self, tiltFactor_balance hh]; ring

def tiltLaw (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i) : FiniteTesting.Probability Ω where
  mass := tiltMass q i σ
  nonneg := tiltMass_nonneg q i σ hh hσ0 hσh
  total := tiltMass_total q i σ hh

@[simp] theorem tiltLaw_mass (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i) (j : Ω) :
    (tiltLaw q i σ hh hσ0 hσh).mass j = tiltMass q i σ j := rfl

theorem tiltLaw_positive (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i)
    (hq : ∀ j, 0 < q.mass j) (hσlt : σ < q.mass i) (j : Ω) :
    0 < (tiltLaw q i σ hh hσ0 hσh).mass j := by
  rw [tiltLaw_mass]
  by_cases hj : j = i
  · subst j
    simpa only [tiltMass_self] using sub_pos.mpr hσlt
  · rw [tiltMass_ne q i σ hj]
    exact mul_pos (lt_of_lt_of_le (by norm_num) (tiltFactor_ge_one hh hσ0)) (hq j)

theorem tiltLaw_chiSquare (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i)
    (hq : ∀ j, 0 < q.mass j) :
    FiniteChiSquare.chiSquare (tiltLaw q i σ hh hσ0 hσh) q =
      σ ^ 2 / (q.mass i * (1 - q.mass i)) := by
  rw [FiniteChiSquare.chiSquare_eq_sum_sq_div _ _ hq]
  have hrest : (∑ j ∈ Finset.univ.erase i,
      ((tiltLaw q i σ hh hσ0 hσh).mass j - q.mass j) ^ 2 / q.mass j) =
      (tiltFactor (q.mass i) σ - 1) ^ 2 * (1 - q.mass i) := by
    rw [← sum_reference_erase q i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [tiltLaw_mass, tiltMass_ne q i σ (Finset.mem_erase.mp hj).1]
    field_simp [ne_of_gt (hq j)]
  calc
    _ = (∑ j ∈ Finset.univ.erase i,
        ((tiltLaw q i σ hh hσ0 hσh).mass j - q.mass j) ^ 2 / q.mass j) +
        ((tiltLaw q i σ hh hσ0 hσh).mass i - q.mass i) ^ 2 / q.mass i :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    _ = _ := by
      rw [hrest, tiltLaw_mass, tiltMass_self]
      unfold tiltFactor
      field_simp [ne_of_gt (hq i), ne_of_gt (sub_pos.mpr hh)]
      ring

theorem tiltLaw_overlap (q : FiniteTesting.Probability Ω) (i : Ω) (σ : ℝ)
    (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i)
    (s : Finset Ω) (hi : i ∈ s) :
    (∑ j ∈ s, min ((tiltLaw q i σ hh hσ0 hσh).mass j) (q.mass j)) =
      (∑ j ∈ s, q.mass j) - σ := by
  have hrest : (∑ j ∈ s.erase i, min ((tiltLaw q i σ hh hσ0 hσh).mass j) (q.mass j)) =
      ∑ j ∈ s.erase i, q.mass j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [tiltLaw_mass, tiltMass_ne q i σ (Finset.mem_erase.mp hj).1, min_eq_right]
    exact le_mul_of_one_le_left (q.nonneg j) (tiltFactor_ge_one hh hσ0)
  have hself : min ((tiltLaw q i σ hh hσ0 hσh).mass i) (q.mass i) = q.mass i - σ := by
    rw [tiltLaw_mass, tiltMass_self, min_eq_left]
    linarith only [hσ0]
  have hp := Finset.sum_erase_add s
    (fun j => min ((tiltLaw q i σ hh hσ0 hσh).mass j) (q.mass j)) hi
  have hqsum := Finset.sum_erase_add s q.mass hi
  dsimp only at hp
  rw [hrest, hself] at hp
  linarith only [hp, hqsum]

omit [DecidableEq Ω] in
theorem chiSquare_productLaw_le_exp (p q : FiniteTesting.Probability Ω) (n : ℕ) :
    FiniteChiSquare.chiSquare (FiniteTesting.productLaw p n) (FiniteTesting.productLaw q n) ≤
      Real.exp ((n : ℝ) * FiniteChiSquare.chiSquare p q) - 1 := by
  have hbase : FiniteChiSquare.likelihoodInner p p q ≤ Real.exp (FiniteChiSquare.chiSquare p q) := by
    change FiniteChiSquare.likelihoodInner p p q ≤
      Real.exp (FiniteChiSquare.likelihoodInner p p q - 1)
    simpa only [sub_add_cancel] using
      Real.add_one_le_exp (FiniteChiSquare.likelihoodInner p p q - 1)
  have hpow := pow_le_pow_left₀ (SignedDiagonalMoment.likelihoodInner_nonneg p p q) hbase n
  rw [← Real.exp_nat_mul] at hpow
  simpa only [FiniteChiSquare.chiSquare, FiniteChiSquare.likelihoodInner_productLaw] using
    sub_le_sub_right hpow 1

omit [DecidableEq Ω] in
theorem productLaw_totalVariation_lt_of_chiSquare_rate (p q : FiniteTesting.Probability Ω)
    (hq : ∀ j, 0 < q.mass j) {T : ℝ} (hT : 0 < T)
    (hrate : FiniteChiSquare.chiSquare p q ≤ 80 / T) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    FiniteTesting.totalVariation (FiniteTesting.productLaw p n) (FiniteTesting.productLaw q n) <
      1 / (10 : ℝ) ^ 5 := by
  have hprod : (n : ℝ) * FiniteChiSquare.chiSquare p q ≤ 80 / (10 : ℝ) ^ 12 := by
    calc
      _ ≤ (n : ℝ) * (80 / T) := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg n)
      _ ≤ _ := by
        rw [show (n : ℝ) * (80 / T) = (80 * n) / T by ring]
        apply (div_le_iff₀ hT).2
        have hn' := mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 80)
        convert hn' using 1; ring
  have hexp := (Real.exp_le_exp.mpr hprod).trans
    (Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 80 / (10 : ℝ) ^ 12) (by norm_num))
  have hchi := chiSquare_productLaw_le_exp p q n
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four
    (FiniteTesting.productLaw p n) (FiniteTesting.productLaw q n)
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  by_contra hnot
  have hlarge : 1 / (10 : ℝ) ^ 5 ≤
      FiniteTesting.totalVariation (FiniteTesting.productLaw p n) (FiniteTesting.productLaw q n) :=
    le_of_not_gt hnot
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 5) hlarge
  norm_num at hexp hsq
  nlinarith only [hexp, hchi, hTV, hsq]

omit [DecidableEq Ω] in
theorem allocation_tilt_coordinate_bound (q : FiniteTesting.Probability Ω) (x : Ω → ℝ)
    {T : ℝ} (hx : ∀ j, 0 ≤ x j ∧ x j < 1)
    (hbudget : T ^ 2 * (∑ j, (q.mass j) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (i : Ω) : T * q.mass i * (x i) ^ 2 ≤ 1 := by
  have hcost : ∀ j, 0 ≤ (q.mass j) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4) := by
    intro j
    exact div_nonneg (by positivity)
      (sub_nonneg.mpr (allocation_fourth_lt_one (hx j).1 (hx j).2).le)
  have hraw : (q.mass i) ^ 2 * (x i) ^ 4 ≤
      (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4) := by
    apply (le_div_iff₀ (sub_pos.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2))).2
    nlinarith only [mul_nonneg (sq_nonneg (q.mass i)) (sq_nonneg ((x i) ^ 4))]
  have hsingle := Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ i)
  have hrawT := mul_le_mul_of_nonneg_left (hraw.trans hsingle) (sq_nonneg T)
  rw [hbudget] at hrawT
  nlinarith only [hrawT, sq_nonneg (T * q.mass i * (x i) ^ 2 - 1)]

theorem tiltLaw_allocation_chiSquare_le (q : FiniteTesting.Probability Ω) (x : Ω → ℝ)
    {T : ℝ} (hT : 0 < T) (hq : ∀ j, 0 < q.mass j)
    (hx : ∀ j, 0 ≤ x j ∧ x j < 1)
    (hbudget : T ^ 2 * (∑ j, (q.mass j) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (i : Ω) (σ : ℝ) (hh : q.mass i < 1) (hσ0 : 0 ≤ σ) (hσh : σ ≤ q.mass i)
    (hcap : q.mass i ≤ (4 : ℝ) / 5) (hσfour : σ ≤ 4 * q.mass i * x i) :
    FiniteChiSquare.chiSquare (tiltLaw q i σ hh hσ0 hσh) q ≤ 80 / T := by
  rw [tiltLaw_chiSquare q i σ hh hσ0 hσh hq]
  apply (div_le_div_iff₀ (mul_pos (hq i) (sub_pos.mpr hh)) hT).2
  have hσsq := pow_le_pow_left₀ hσ0 hσfour 2
  have hσT := mul_le_mul_of_nonneg_left hσsq hT.le
  have hdisp := mul_le_mul_of_nonneg_left
    (allocation_tilt_coordinate_bound q x hx hbudget i)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (hq i).le)
  have hcap' := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) (hq i).le) (sub_nonneg.mpr hcap)
  nlinarith only [hσT, hdisp, hcap']

/-- A concrete positive tilt is constructed whenever the paired branch's
largest-displacement condition fails. The selected point is obtained from that
failure; no argmax, permutation, or chi-square certificate is an input. -/
theorem exists_tilt_of_dominant_displacement
    (q : FiniteTesting.Probability Ω) (x : Ω → ℝ) (s : Finset Ω)
    {T : ℝ} (hT : 0 < T) (hq : ∀ j, 0 < q.mass j)
    (hx : ∀ j, 0 ≤ x j ∧ x j < 1) (hcap : ∀ j, q.mass j ≤ (4 : ℝ) / 5)
    (hsmall : ∀ j ∈ s, x j ≤ (1 : ℝ) / 8)
    (hbudget : T ^ 2 * (∑ j, (q.mass j) ^ 2 * (x j) ^ 4 / (1 - (x j) ^ 4)) = 1)
    (hnot : ¬ ∀ i ∈ s, q.mass i * x i ≤ (∑ j ∈ s, q.mass j * x j) / 2) :
    ∃ (i : Ω) (ν : FiniteTesting.Probability Ω) (f : ℝ), i ∈ s ∧
      1 ≤ f ∧ f ≤ 3 ∧ (∀ j, 0 < ν.mass j) ∧
      ν.mass i = q.mass i - 2 * (∑ j ∈ s, q.mass j * x j) ∧
      (∀ j, j ≠ i → ν.mass j = f * q.mass j) ∧
      (∑ j ∈ s, min (ν.mass j) (q.mass j)) =
        (∑ j ∈ s, q.mass j) - 2 * (∑ j ∈ s, q.mass j * x j) ∧
      FiniteChiSquare.chiSquare ν q ≤ 80 / T ∧
      (∀ n : ℕ, (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T →
        FiniteTesting.totalVariation (FiniteTesting.productLaw ν n) (FiniteTesting.productLaw q n) <
          1 / (10 : ℝ) ^ 5) := by
  obtain ⟨i, hi, hdom⟩ : ∃ i ∈ s, (∑ j ∈ s, q.mass j * x j) / 2 < q.mass i * x i := by
    simpa only [not_forall, not_le, exists_prop] using hnot
  let σ : ℝ := 2 * (∑ j ∈ s, q.mass j * x j)
  have hσ0 : 0 ≤ σ := mul_nonneg (by norm_num)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (q.nonneg j) (hx j).1))
  have hσfour : σ < 4 * q.mass i * x i := by dsimp [σ]; linarith only [hdom]
  have hσhalf : σ ≤ q.mass i / 2 := by
    have h := mul_le_mul_of_nonneg_left (hsmall i hi) (q.nonneg i)
    nlinarith only [h, hσfour.le]
  have hh : q.mass i < 1 := by linarith only [hcap i]
  have hσlt : σ < q.mass i := by linarith only [hσhalf, hq i]
  let ν := tiltLaw q i σ hh hσ0 hσlt.le
  have hchi : FiniteChiSquare.chiSquare ν q ≤ 80 / T :=
    tiltLaw_allocation_chiSquare_le q x hT hq hx hbudget i σ hh hσ0 hσlt.le (hcap i) hσfour.le
  refine ⟨i, ν, tiltFactor (q.mass i) σ, hi, tiltFactor_ge_one hh hσ0,
    tiltFactor_le_three (hcap i) hσhalf,
    tiltLaw_positive q i σ hh hσ0 hσlt.le hq hσlt, ?_, ?_, ?_, hchi, ?_⟩
  · exact tiltMass_self q i σ
  · intro j hj
    exact tiltMass_ne q i σ hj
  · exact tiltLaw_overlap q i σ hh hσ0 hσlt.le s hi
  · intro n hn
    exact productLaw_totalVariation_lt_of_chiSquare_rate ν q hq hT hchi n hn

/-- The tilt construction is connected to coordinates constructed at the
original allocation root, under the original no-heavy-atom hypothesis. -/
theorem exists_original_root_dominant_tilt {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (hq : ∀ j, 0 < q.mass j)
    (hcap : ∀ j, q.mass j ≤ (4 : ℝ) / 5) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < allocationRoot (extendFiniteLaw q) r ∧
      ∃ x : Fin k → ℝ, (∀ j, 0 < x j ∧ x j < 1) ∧ (∑ j, q.mass j * x j) = r ∧
        (∀ s : Finset (Fin k), (∀ j ∈ s, x j ≤ (1 : ℝ) / 8) →
          (¬ ∀ i ∈ s, q.mass i * x i ≤ (∑ j ∈ s, q.mass j * x j) / 2) →
          ∃ (i : Fin k) (ν : FiniteTesting.Probability (Fin k)) (f : ℝ), i ∈ s ∧
            1 ≤ f ∧ f ≤ 3 ∧ (∀ j, 0 < ν.mass j) ∧
            ν.mass i = q.mass i - 2 * (∑ j ∈ s, q.mass j * x j) ∧
            (∀ j, j ≠ i → ν.mass j = f * q.mass j) ∧
            (∑ j ∈ s, min (ν.mass j) (q.mass j)) =
              (∑ j ∈ s, q.mass j) - 2 * (∑ j ∈ s, q.mass j * x j) ∧
            FiniteChiSquare.chiSquare ν q ≤ 80 / allocationRoot (extendFiniteLaw q) r ∧
            (∀ n : ℕ, (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * allocationRoot (extendFiniteLaw q) r →
              FiniteTesting.totalVariation (FiniteTesting.productLaw ν n) (FiniteTesting.productLaw q n) <
                1 / (10 : ℝ) ^ 5)) := by
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, hfinal⟩ :=
    exists_finite_allocation_coordinates_at_root q hq hr0 hr1
  refine ⟨hT, x, hx, hsum, ?_⟩
  intro s hs hnot
  exact exists_tilt_of_dominant_displacement q x s hT hq
    (fun j => ⟨(hx j).1.le, (hx j).2⟩) hcap hs hbudget hnot

end IdentityTesting.DominantTilt
