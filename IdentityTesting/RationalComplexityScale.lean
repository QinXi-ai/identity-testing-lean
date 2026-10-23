import IdentityTesting.RationalReferenceOrdering
import IdentityTesting.RationalAllocationRoot
import IdentityTesting.HeavyRootOracle
import IdentityTesting.RationalScaleIntervals

/-! Executable factor-two evaluation of the original real characterization
scale for explicitly listed positive rational references. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def rationalHeavyInterval : {k : ℕ} → (Fin (k + 1) → ℚ) → ℚ → ℚ × ℚ
  | 0, _, _ => (0, 0)
  | k + 1, q, e => heavyRootOracle (rationalTail q) e

def rationalComplexityInterval {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) : ℚ × ℚ :=
  let h := rationalMaxValue q
  let R := 1 - h
  if e = 1 then (0, 0)
  else if h = 1 then (1 / e, 1 / e)
  else if 3 / 4 < h then
    if e ≤ R then rationalHeavyInterval q e
    else intervalMin (rationalHeavyInterval q R) (R / (e - R) ^ 2 + 1 / (e - R))
  else if h / 2 ≤ 1 - e then rationalAllocationRootInterval q e
  else rationalMomentInterval q (1 - e)

noncomputable section

theorem rationalHeavyInterval_spec {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1)
    (hh : (3 / 4 : ℚ) ≤ rationalMaxValue q) (hne : rationalMaxValue q ≠ 1) (he : 0 < e) :
    RootIntervalValid
      (heavyRoot (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e)
      (rationalHeavyInterval q e) := by
  cases k with
  | zero =>
      have hq0 : q 0 = 1 := by simpa using hs
      have hmax : rationalMaxValue q = 1 := by
        obtain ⟨i, hi⟩ := rationalMaxValue_attained q
        have hi0 : i = 0 := by apply Fin.ext; omega
        simpa only [hi0, hq0] using hi.symm
      exact False.elim (hne hmax)
  | succ k =>
      have hhR : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0 := by
        rw [rationalHeadFirst_head]
        simpa only [Rat.cast_div, Rat.cast_ofNat] using
          (Rat.cast_le.mpr hh : (((3 / 4 : ℚ) : ℝ)) ≤ (rationalMaxValue q : ℝ))
      rw [rationalHeadFirst_heavyRoot q hq hs hhR]
      exact heavyRootOracle_spec (rationalTail q) e (rationalTail_pos q hq) he

theorem rationalComplexityInterval_positive_spec {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (he : 0 < e) (he1 : e < 1) :
    RootIntervalValid
      (complexityScale (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e)
      (rationalComplexityInterval q e) := by
  let p := extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)
  let h := rationalMaxValue q
  have hmax : largestMass p = (h : ℝ) := by
    exact (rationalOriginal_largestMass q hq hs).trans (by rw [rationalHeadFirst_head])
  have hle : h ≤ 1 := by
    obtain ⟨i, hi⟩ := rationalMaxValue_attained q
    rw [show h = q i from hi.symm, ← hs]
    exact Finset.single_le_sum (fun j _ => (hq j).le) (Finset.mem_univ i)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have he1R : (e : ℝ) < 1 := by exact_mod_cast he1
  have hne1 : e ≠ 1 := ne_of_lt he1
  change RootIntervalValid (complexityScale p e) _
  unfold complexityScale
  rw [hmax]
  simp only [ne_of_lt he1R, if_false]
  unfold rationalComplexityInterval
  simp only [hne1, if_false]
  change RootIntervalValid _
    (if h = 1 then (1 / e, 1 / e)
    else if (3 / 4 : ℚ) < h then
      if e ≤ 1 - h then rationalHeavyInterval q e
      else intervalMin (rationalHeavyInterval q (1 - h))
        ((1 - h) / (e - (1 - h)) ^ 2 + 1 / (e - (1 - h)))
    else if h / 2 ≤ 1 - e then rationalAllocationRootInterval q e
    else rationalMomentInterval q (1 - e))
  by_cases hp : h = 1
  · have hpR : (h : ℝ) = 1 := by exact_mod_cast hp
    simp only [hp, hpR, if_true]
    simpa only [Rat.cast_div, Rat.cast_one] using rootInterval_singleton (1 / e) (one_div_pos.mpr he)
  · have hpR : (h : ℝ) ≠ 1 := by exact_mod_cast hp
    simp only [hp, hpR, if_false]
    have hR : (0 : ℚ) < 1 - h := sub_pos.mpr (lt_of_le_of_ne hle hp)
    by_cases hh : (3 / 4 : ℚ) < h
    · have hhR : (3 / 4 : ℝ) < (h : ℝ) := by
        simpa only [Rat.cast_div, Rat.cast_ofNat] using
          (Rat.cast_lt.mpr hh : (((3 / 4 : ℚ) : ℝ)) < (h : ℝ))
      simp only [hh, hhR, if_true]
      by_cases hin : e ≤ 1 - h
      · have hinR : (e : ℝ) ≤ 1 - (h : ℝ) := by exact_mod_cast hin
        simp only [hin, hinR, if_true]
        exact rationalHeavyInterval_spec q e hq hs hh.le hp he
      · have hinR : ¬ (e : ℝ) ≤ 1 - (h : ℝ) := by exact_mod_cast hin
        simp only [hin, hinR, if_false]
        have hd : 0 < e - (1 - h) := sub_pos.mpr (lt_of_not_ge hin)
        have hb : 0 < (1 - h) / (e - (1 - h)) ^ 2 + 1 / (e - (1 - h)) := by positivity
        have hbkt := rootInterval_min _ (rationalHeavyInterval_spec q (1 - h) hq hs hh.le hp hR) hb
        simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_div, Rat.cast_pow] using hbkt
    · have hhR : ¬ (3 / 4 : ℝ) < (h : ℝ) := by
        have hle' : h ≤ (3 / 4 : ℚ) := le_of_not_gt hh
        have hleR : (h : ℝ) ≤ (3 / 4 : ℝ) := by
          simpa only [Rat.cast_div, Rat.cast_ofNat] using
            (Rat.cast_le.mpr hle' : (h : ℝ) ≤ (((3 / 4 : ℚ) : ℝ)))
        exact not_lt_of_ge hleR
      simp only [hh, hhR, if_false]
      by_cases ha : h / 2 ≤ 1 - e
      · have haR : (h : ℝ) / 2 ≤ 1 - (e : ℝ) := by exact_mod_cast ha
        simp only [ha, haR, if_true]
        exact rationalAllocationRootInterval_spec q e hq hs he he1
      · have haR : ¬ (h : ℝ) / 2 ≤ 1 - (e : ℝ) := by exact_mod_cast ha
        simp only [ha, haR, if_false]
        obtain ⟨hl, hvL, hvU, hwidth⟩ := rationalMomentInterval_spec q (1 - e) hq hs (sub_pos.mpr he1)
        exact ⟨hl, by simpa only [Rat.cast_sub, Rat.cast_one] using hvL,
          by simpa only [Rat.cast_sub, Rat.cast_one] using hvU, hwidth.le⟩

theorem rationalComplexityInterval_spec {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (he : 0 < e) (he1 : e ≤ 1) :
    ScaleIntervalValid
      (complexityScale (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e)
      (rationalComplexityInterval q e) := by
  rcases lt_or_eq_of_le he1 with heLt | rfl
  · exact (rationalComplexityInterval_positive_spec q e hq hs he heLt).to_scale
  · simpa only [rationalComplexityInterval, complexityScale, Rat.cast_zero, Rat.cast_one, if_true] using
      scaleInterval_singleton 0 le_rfl

theorem rationalComplexityInterval_at_one {k : ℕ} (q : Fin (k + 1) → ℚ) :
    rationalComplexityInterval q 1 = (0, 0) := by simp [rationalComplexityInterval]

end
end IdentityTesting.RationalComputation
