import IdentityTesting.AllocationRootQuantitative
import IdentityTesting.HeavyRoots
import IdentityTesting.OverlapMoment

noncomputable section
namespace IdentityTesting

theorem heavyRoot_ge_tail_div_sq (q : DiscreteLaw) (hq : largestMass q < 1)
    {e : ℝ} (he : 0 < e) : (1 - largestMass q) / e ^ 2 ≤ heavyRoot q e := by
  have hT := heavyRoot_pos q hq he
  have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
  have hd := (allocationD_bounds (heavyRoot q e) (tailMasses_nonneg q)
    (tailMasses_summable q)).1
  have heq := heavyRoot_equation q hq he
  have hsq := Real.sq_sqrt (div_pos hR hT).le
  have hg : Real.sqrt ((1 - largestMass q) / heavyRoot q e) ≤ e := by linarith
  have hratio : (1 - largestMass q) / heavyRoot q e ≤ e ^ 2 := by
    nlinarith [Real.sqrt_nonneg ((1 - largestMass q) / heavyRoot q e)]
  have hmul := (div_le_iff₀ hT).mp hratio
  apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
  nlinarith only [hmul]

theorem heavyRoot_ge_inv_tail (q : DiscreteLaw) (hq : largestMass q < 1)
    {e : ℝ} (he : 0 < e) (heR : e ≤ 1 - largestMass q) :
    1 / (1 - largestMass q) ≤ heavyRoot q e := by
  have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
  calc
    _ = (1 - largestMass q) / (1 - largestMass q) ^ 2 := by field_simp
    _ ≤ (1 - largestMass q) / e ^ 2 :=
      div_le_div_of_nonneg_left hR.le (sq_pos_of_pos he) (pow_le_pow_left₀ he.le heR 2)
    _ ≤ _ := heavyRoot_ge_tail_div_sq q hq he

theorem complexityScale_ge_one (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) : 1 ≤ complexityScale q ε := by
  have hεne : ε ≠ 1 := ne_of_lt hε1
  unfold complexityScale
  simp only [hεne, if_false]
  split_ifs with hpoint hheavy hin halloc
  · exact (le_div_iff₀ hε0).mpr (by simpa using hε1.le)
  · have hq := lt_of_le_of_ne (largestMass_le_one q) hpoint
    have hR := sub_pos.mpr hq
    have hR1 : 1 - largestMass q ≤ 1 := by linarith [largestMass_pos q]
    exact ((le_div_iff₀ hR).mpr (by simpa using hR1)).trans
      (heavyRoot_ge_inv_tail q hq hε0 hin)
  · have hq := lt_of_le_of_ne (largestMass_le_one q) hpoint
    have hR := sub_pos.mpr hq
    have hR1 : 1 - largestMass q ≤ 1 := by linarith [largestMass_pos q]
    apply le_min
    · exact ((le_div_iff₀ hR).mpr (by simpa using hR1)).trans
        (heavyRoot_ge_inv_tail q hq hR le_rfl)
    · have hg : 0 < ε - (1 - largestMass q) := sub_pos.mpr (lt_of_not_ge hin)
      have hg1 : ε - (1 - largestMass q) ≤ 1 := by linarith
      have hi : 1 ≤ 1 / (ε - (1 - largestMass q)) :=
        (le_div_iff₀ hg).mpr (by simpa using hg1)
      exact hi.trans (le_add_of_nonneg_left (div_nonneg hR.le (sq_nonneg _)))
  · have hb := allocationRoot_sharp_rounding q hε0 hε1 halloc
    have hT := (allocationRoot_spec q hε0 hε1).1
    nlinarith only [hb.1, hb.2.1, hT]
  · exact (le_div_iff₀ (overlapMoment_pos q (sub_pos.mpr hε1))).mpr
      (by simpa using overlapMoment_le_one q (1 - ε))

theorem roundedScale_le_twice_complexityScale (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (roundedScale q ε : ℝ) ≤ 2 * complexityScale q ε := by
  have h := complexityScale_ge_one q hε0 hε1
  have hc := Nat.ceil_lt_add_one (show 0 ≤ complexityScale q ε by linarith)
  change (⌈complexityScale q ε⌉₊ : ℝ) ≤ _
  linarith

end IdentityTesting
