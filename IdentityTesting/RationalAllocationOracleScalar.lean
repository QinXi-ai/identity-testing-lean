import IdentityTesting.RationalBisection
import IdentityTesting.AllocationFiniteBridge

/-! # Algebraic bounds used by the executable rational allocation oracle -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem fourth_difference_bounds {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    4 * l ^ 3 * (u - l) ≤ u ^ 4 - l ^ 4 ∧
      u ^ 4 - l ^ 4 ≤ 4 * (u - l) := by
  have hu0 : 0 ≤ u := hl.trans hlu
  have hl1 : l ≤ 1 := hlu.trans hu
  have hl2 := pow_le_one₀ hl hl1 (n := 2)
  have hu2 := pow_le_one₀ hu0 hu (n := 2)
  have hl3 := pow_le_one₀ hl hl1 (n := 3)
  have hu3 := pow_le_one₀ hu0 hu (n := 3)
  have hul : u ^ 2 * l ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hu2 hl1 hl (by norm_num : (0 : ℝ) ≤ 1)
  have hlu2 : u * l ^ 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hu hl2 (sq_nonneg l) (by norm_num : (0 : ℝ) ≤ 1)
  have hSupper : u ^ 3 + u ^ 2 * l + u * l ^ 2 + l ^ 3 ≤ 4 := by
    linarith only [hu3, hul, hlu2, hl3]
  have h3 := pow_le_pow_left₀ hl hlu 3
  have h2 := pow_le_pow_left₀ hl hlu 2
  have h21 := mul_le_mul_of_nonneg_right h2 hl
  have h12 := mul_le_mul_of_nonneg_right hlu (sq_nonneg l)
  have hSlower : 4 * l ^ 3 ≤ u ^ 3 + u ^ 2 * l + u * l ^ 2 + l ^ 3 := by
    nlinarith only [h3, h21, h12]
  have hid : u ^ 4 - l ^ 4 = (u - l) * (u ^ 3 + u ^ 2 * l + u * l ^ 2 + l ^ 3) := by ring
  constructor
  · rw [hid]
    have h := mul_le_mul_of_nonneg_left hSlower (sub_nonneg.mpr hlu)
    nlinarith only [h]
  · rw [hid]
    have h := mul_le_mul_of_nonneg_left hSupper (sub_nonneg.mpr hlu)
    nlinarith only [h]

theorem allocationCost_difference {t a l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1) :
    allocationCost t a u - allocationCost t a l =
      t ^ 2 * a ^ 2 * (u ^ 4 - l ^ 4) / ((1 - u ^ 4) * (1 - l ^ 4)) := by
  have hdl : 1 - l ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hl (hlu.trans_lt hu)))
  have hdu : 1 - u ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one (hl.trans hlu) hu))
  unfold allocationCost
  field_simp [hdl, hdu]
  ring

theorem allocationCost_mono {t a l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1) :
    allocationCost t a l ≤ allocationCost t a u := by
  have hpow := pow_le_pow_left₀ hl hlu 4
  have hdl : 0 < 1 - l ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hl (hlu.trans_lt hu))
  have hdu : 0 < 1 - u ^ 4 := sub_pos.mpr (allocation_fourth_lt_one (hl.trans hlu) hu)
  have h := div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg a)) (sub_nonneg.mpr hpow))
    (mul_nonneg hdu.le hdl.le)
  rw [← allocationCost_difference hl hlu hu] at h
  linarith only [h]

theorem allocationCost_lipschitz {t a l u ρ : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hρ : 0 < ρ) (hu : u ≤ 1 - ρ) :
    allocationCost t a u - allocationCost t a l ≤
      (4 * t ^ 2 * a ^ 2 / ρ ^ 2) * (u - l) := by
  have hu1 : u < 1 := by linarith only [hu, hρ]
  have hu0 : 0 ≤ u := hl.trans hlu
  have hl1 : l ≤ 1 := (hlu.trans hu1.le)
  have hup := pow_le_of_le_one hu0 hu1.le (by norm_num : (4 : ℕ) ≠ 0)
  have hlp := pow_le_of_le_one hl hl1 (by norm_num : (4 : ℕ) ≠ 0)
  have hdu : ρ ≤ 1 - u ^ 4 := by linarith only [hup, hu]
  have hdl : ρ ≤ 1 - l ^ 4 := by linarith only [hlp, hlu, hu]
  have hden : ρ ^ 2 ≤ (1 - u ^ 4) * (1 - l ^ 4) := by
    have h := mul_le_mul hdu hdl hρ.le (hρ.le.trans hdu)
    nlinarith only [h]
  have hn0 : 0 ≤ t ^ 2 * a ^ 2 * (u ^ 4 - l ^ 4) :=
    mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg a))
      (sub_nonneg.mpr (pow_le_pow_left₀ hl hlu 4))
  rw [allocationCost_difference hl hlu hu1]
  calc
    _ ≤ t ^ 2 * a ^ 2 * (u ^ 4 - l ^ 4) / ρ ^ 2 :=
      div_le_div_of_nonneg_left hn0 (sq_pos_of_pos hρ) hden
    _ ≤ t ^ 2 * a ^ 2 * (4 * (u - l)) / ρ ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fourth_difference_bounds hl hlu hu1.le).2
          (mul_nonneg (sq_nonneg t) (sq_nonneg a))) (sq_nonneg ρ)
    _ = _ := by ring

theorem stationary_coordinate_parameter_mono {a β γ x y : ℝ}
    (ha : 0 < a) (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hβγ : β ≤ γ)
    (hx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hy : a * y ^ 3 = γ * (1 - y ^ 4) ^ 2) : x ≤ y := by
  have hxshape := allocation_stationarity_shape hx0 hx1 hx
  have hyshape := allocation_stationarity_shape hy0 hy1 hy
  by_contra hnot
  have hshape := allocationKktShape_lt hy0 (lt_of_not_ge hnot) hx1
  have h := mul_lt_mul_of_pos_left hshape ha
  rw [hxshape, hyshape] at h
  exact (not_lt_of_ge hβγ) h

theorem stationary_coordinate_ratio {a β γ x y : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2)
    (hy : a * y ^ 3 = γ * (1 - y ^ 4) ^ 2) : β * y ≤ γ * x := by
  have hγ : 0 < γ := hβ.trans_le hβγ
  have hxy := stationary_coordinate_parameter_mono ha hx0 hx1 hy0 hy1 hβγ hx hy
  have hdy : 0 ≤ 1 - y ^ 4 := (sub_pos.mpr (allocation_fourth_lt_one hy0.le hy1)).le
  have hdle : (1 - y ^ 4) ^ 2 ≤ (1 - x ^ 4) ^ 2 := by
    have hp := pow_le_pow_left₀ hx0.le hxy 4
    exact pow_le_pow_left₀ hdy (by linarith only [hp]) 2
  have hbase : β * y ^ 3 ≤ γ * x ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hdle (mul_nonneg hβ.le hγ.le)
    have hleft : a * (β * y ^ 3) = (β * γ) * (1 - y ^ 4) ^ 2 := by
      calc
        _ = β * (a * y ^ 3) := by ring
        _ = _ := by rw [hy]; ring
    have hright : a * (γ * x ^ 3) = (β * γ) * (1 - x ^ 4) ^ 2 := by
      calc
        _ = γ * (a * x ^ 3) := by ring
        _ = _ := by rw [hx]; ring
    rw [← hleft, ← hright] at h
    exact (mul_le_mul_iff_right₀ ha).mp h
  have hpow : (β * y) ^ 3 ≤ (γ * x) ^ 3 := by
    calc
      _ = β ^ 2 * (β * y ^ 3) := by ring
      _ ≤ β ^ 2 * (γ * x ^ 3) := mul_le_mul_of_nonneg_left hbase (sq_nonneg β)
      _ ≤ γ ^ 2 * (γ * x ^ 3) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hβ.le hβγ 2) (by positivity)
      _ = _ := by ring
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) hpow

theorem allocationCost_stationary_tangent {t a β l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1)
    (hstationary : a * l ^ 3 = β * (1 - l ^ 4) ^ 2) :
    4 * t ^ 2 * β * (a * (u - l)) ≤ allocationCost t a u - allocationCost t a l := by
  have hdl : 0 < 1 - l ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hl.le (hlu.trans_lt hu))
  have hdu : 0 < 1 - u ^ 4 := sub_pos.mpr (allocation_fourth_lt_one (hl.le.trans hlu) hu)
  have hden : (1 - u ^ 4) * (1 - l ^ 4) ≤ (1 - l ^ 4) ^ 2 := by
    have hp := pow_le_pow_left₀ hl.le hlu 4
    have h := mul_le_mul_of_nonneg_right (show 1 - u ^ 4 ≤ 1 - l ^ 4 by linarith only [hp]) hdl.le
    nlinarith only [h]
  have hquot : a * l ^ 3 / (1 - l ^ 4) ^ 2 = β :=
    (div_eq_iff (ne_of_gt (pow_pos hdl 2))).2 hstationary
  rw [allocationCost_difference hl.le hlu hu]
  calc
    _ = t ^ 2 * a ^ 2 * (4 * l ^ 3 * (u - l)) / (1 - l ^ 4) ^ 2 := by
      calc
        _ = 4 * t ^ 2 * a * (a * l ^ 3 / (1 - l ^ 4) ^ 2) * (u - l) := by rw [hquot]; ring
        _ = _ := by ring
    _ ≤ t ^ 2 * a ^ 2 * (u ^ 4 - l ^ 4) / (1 - l ^ 4) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (fourth_difference_bounds hl.le hlu hu.le).1
          (mul_nonneg (sq_nonneg t) (sq_nonneg a))) (sq_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg a))
        (sub_nonneg.mpr (pow_le_pow_left₀ hl.le hlu 4))) (mul_pos hdu hdl) hden

end IdentityTesting.RationalComputation
