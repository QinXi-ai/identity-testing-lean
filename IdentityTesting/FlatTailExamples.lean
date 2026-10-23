import IdentityTesting.EqualBlockAllocation
import IdentityTesting.HeavyFiniteBridge
import IdentityTesting.CountableCharacterizationRealScale

/-! Concrete point-head / flat-tail references from `01_main.tex`.
The head selection and shifted tail embedding are connected to the original
definitions of `largestMass`, `tailMasses`, and `heavyRoot`. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting
open HeavySignedFamily

def flatTailFiniteLaw (k : ℕ) (hk : 0 < k) (R : ℝ)
    (hR0 : 0 ≤ R) (hR1 : R ≤ 1) : FiniteTesting.Probability (Fin (k + 1)) where
  mass := Fin.cases (1 - R) (fun _ => R / (k : ℝ))
  nonneg := by
    intro i
    refine Fin.cases (sub_nonneg.mpr hR1) (fun _ => ?_) i
    exact div_nonneg hR0 (Nat.cast_nonneg k)
  total := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

def flatTailLaw (k : ℕ) (hk : 0 < k) (R : ℝ) (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    DiscreteLaw := extendFiniteLaw (flatTailFiniteLaw k hk R hR0 hR1)

@[simp] theorem flatTailFiniteLaw_tailTotal {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1) :
    tailTotal (flatTailFiniteLaw k hk R hR0 hR1) = R := by
  simp only [tailTotal, flatTailFiniteLaw, Fin.cases_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem flatTailLaw_largestMass {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R ≤ 1) (hR : R ≤ 1 / 4) :
    largestMass (flatTailLaw k hk R hR0 hR1) = 1 - R := by
  have htail : tailTotal (flatTailFiniteLaw k hk R hR0 hR1) ≤ (1 : ℝ) / 4 := by
    simpa using hR
  exact largestMass_extendFiniteLaw_heavy _ htail

/-- Exact tail allocation for the actual head-and-tail probability law. -/
theorem flatTail_allocationD {k : ℕ} (hk : 0 < k)
    {R t : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hR : R ≤ 1 / 4) (ht : 0 < t) :
    allocationD (tailMasses (flatTailLaw k hk R hR0.le hR1)) t =
      R * (1 + t ^ 2 * R ^ 2 / k) ^ (-1 / 4 : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have htail : tailTotal (flatTailFiniteLaw k hk R hR0.le hR1) ≤ (1 : ℝ) / 4 := by
    simpa using hR
  rw [flatTailLaw, tailMasses_extendFiniteLaw_heavy _ htail]
  change allocationD (extendFiniteTailVector (fun _ : Fin k => R / (k : ℝ))) t = _
  rw [allocationD_extendFiniteTailVector_eq_optimizer ht (fun _ => div_pos hR0 hkpos)
    (u := fun _ => 1 / (k : ℝ))]
  · exact equal_block_unit_objective hk ht hR0
  · exact ⟨fun _ => by positivity, by simp [ne_of_gt hkpos]⟩
  · exact fun u hu0 hu1 => equal_mass_allocation_maximum hk ht
      (div_pos hR0 hkpos) u hu0 hu1

/-- At the original boundary heavy root, `z=R*B(R)` satisfies the normalized
equation in the flat-tail example. `1/sqrt(z)` is exactly `z^(-1/2)` for z>0. -/
theorem flatTail_boundary_root_equation {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hR : R ≤ 1 / 4) :
    let q := flatTailLaw k hk R hR0.le hR1
    let z := R * heavyRoot q R
    0 < z ∧ (1 + z ^ 2 / k) ^ (-1 / 4 : ℝ) + 1 / Real.sqrt z = 1 := by
  let q := flatTailLaw k hk R hR0.le hR1
  let T := heavyRoot q R
  have hlarge : largestMass q < 1 := by
    rw [flatTailLaw_largestMass hk hR0.le hR1 hR]
    linarith
  have ht : 0 < T := heavyRoot_pos q hlarge hR0
  have heq := heavyRoot_equation q hlarge hR0
  change allocationD (tailMasses q) T + Real.sqrt ((1 - largestMass q) / T) = R at heq
  rw [flatTail_allocationD hk hR0 hR1 hR ht,
    flatTailLaw_largestMass hk hR0.le hR1 hR] at heq
  have hsqrt : Real.sqrt (R / T) = R * (1 / Real.sqrt (R * T)) := by
    have hratio : R / T = R ^ 2 * (1 / (R * T)) := by field_simp
    rw [hratio, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR0.le,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  refine ⟨mul_pos hR0 ht, ?_⟩
  change (1 + (R * T) ^ 2 / k) ^ (-1 / 4 : ℝ) + 1 / Real.sqrt (R * T) = 1
  apply mul_left_cancel₀ (ne_of_gt hR0)
  have hpoly : (R * T) ^ 2 = T ^ 2 * R ^ 2 := by ring
  rw [hpoly, mul_add, mul_one]
  simpa only [sub_sub_cancel, hsqrt] using heq

/-- Explicit constants for the truncated linear deficit used in the flat-tail
example. This proves the comparison for all positive real `s`. -/
theorem quarter_power_deficit_bounds {s : ℝ} (hs : 0 < s) :
    min s 1 / 8 ≤ 1 - (1 + s) ^ (-1 / 4 : ℝ) ∧
      1 - (1 + s) ^ (-1 / 4 : ℝ) ≤ min s 1 := by
  let x := (1 + s) ^ (-1 / 4 : ℝ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1.le)]
  have hx3 : x ^ 3 ≤ 1 := (pow_le_pow_left₀ hx0.le hx1.le 3).trans_eq (by norm_num)
  let P := 1 + x + x ^ 2 + x ^ 3
  have hP0 : 1 ≤ P := by dsimp [P]; nlinarith [sq_nonneg x, pow_nonneg hx0.le 3]
  have hP4 : P ≤ 4 := by dsimp [P]; linarith
  have hD : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
  have hp : x ^ 4 = (1 + s)⁻¹ := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 1 + s)]
    norm_num [Real.rpow_neg_one]
  have hproduct : (1 + s) * x ^ 4 = 1 := by
    rw [hp]; exact mul_inv_cancel₀ (by linarith)
  have hfactor : s = ((1 + s) * P) * (1 - x) := by
    dsimp [P]
    nlinarith [hproduct]
  have hbase : 1 ≤ (1 + s) * P := by nlinarith
  have hupperS : 1 - x ≤ s := by
    have h := mul_le_mul_of_nonneg_right hbase hD
    rw [← hfactor] at h
    simpa using h
  change min s 1 / 8 ≤ 1 - x ∧ 1 - x ≤ min s 1
  refine ⟨?_, le_min hupperS (by linarith)⟩
  by_cases hs1 : s ≤ 1
  · rw [min_eq_left hs1]
    have hbound : (1 + s) * P ≤ 8 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hbound hD
    rw [← hfactor] at h
    linarith
  · rw [min_eq_right (le_of_not_ge hs1)]
    have hs1' : 1 ≤ s := le_of_not_ge hs1
    have hbound : (1 + s) * P ≤ 8 * s := by nlinarith
    have h := mul_le_mul_of_nonneg_right hbound hD
    rw [← hfactor] at h
    have hd : 1 ≤ 8 * (1 - x) := by nlinarith
    linarith

/-- The normalized flat-tail equation forces the two-fifths scale. Explicit
constants are uniform over all positive integer block sizes. -/
theorem flat_tail_scalar_root_bounds {k : ℕ} (hk : 0 < k) {z : ℝ}
    (hz : 0 < z)
    (heq : (1 + z ^ 2 / k) ^ (-1 / 4 : ℝ) + 1 / Real.sqrt z = 1) :
    (k : ℝ) ^ (2 / 5 : ℝ) ≤ z ∧ z ≤ 64 * (k : ℝ) ^ (2 / 5 : ℝ) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hspos : 0 < z ^ 2 / k := div_pos (sq_pos_of_pos hz) hkpos
  have hbounds := quarter_power_deficit_bounds hspos
  have hdef : 1 - (1 + z ^ 2 / k) ^ (-1 / 4 : ℝ) = 1 / Real.sqrt z := by linarith
  rw [hdef] at hbounds
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hpower : z ^ 2 * Real.sqrt z = z ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hz]
    norm_num
  have hl : (k : ℝ) ≤ z ^ (5 / 2 : ℝ) := by
    have h := hbounds.2.trans (min_le_left _ _)
    have hm := (div_le_div_iff₀ hsz hkpos).1 h
    simpa only [one_mul, hpower] using hm
  have hl' := Real.rpow_le_rpow (Nat.cast_nonneg k) hl (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [← Real.rpow_mul hz.le] at hl'
  norm_num at hl'
  refine ⟨hl', ?_⟩
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpow : 1 ≤ (k : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hkone (by norm_num)
  by_cases hs1 : z ^ 2 / k ≤ 1
  · rw [min_eq_left hs1] at hbounds
    have h : z ^ 2 / k ≤ 8 / Real.sqrt z := by
      calc
        z ^ 2 / k = 8 * (z ^ 2 / k / 8) := by ring
        _ ≤ 8 * (1 / Real.sqrt z) := mul_le_mul_of_nonneg_left hbounds.1 (by norm_num)
        _ = 8 / Real.sqrt z := by ring
    have hm := (div_le_div_iff₀ hkpos hsz).1 h
    rw [hpower] at hm
    have hu := Real.rpow_le_rpow (Real.rpow_nonneg hz.le _) hm
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [← Real.rpow_mul hz.le, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8)
      (Nat.cast_nonneg k)] at hu
    norm_num at hu
    have hc : (8 : ℝ) ^ (2 / 5 : ℝ) ≤ 8 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg k) (2 / 5 : ℝ))
    nlinarith
  · rw [min_eq_right (le_of_not_ge hs1)] at hbounds
    have h : Real.sqrt z ≤ 8 := by
      have hm := (le_div_iff₀ hsz).1 hbounds.1
      linarith
    have hz64 : z ≤ 64 := by nlinarith [Real.sq_sqrt hz.le, Real.sqrt_nonneg z]
    linarith

/-- Actual boundary root estimate in the flat-tail example, with all scalar
equation hypotheses supplied by the original probability law and root. -/
theorem flatTail_boundary_heavyRoot_bounds {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR0 : 0 < R) (hR1 : R ≤ 1) (hR : R ≤ 1 / 4) :
    (k : ℝ) ^ (2 / 5 : ℝ) / R ≤ heavyRoot (flatTailLaw k hk R hR0.le hR1) R ∧
      heavyRoot (flatTailLaw k hk R hR0.le hR1) R ≤ 64 * (k : ℝ) ^ (2 / 5 : ℝ) / R := by
  have h := flatTail_boundary_root_equation hk hR0 hR1 hR
  have hb := flat_tail_scalar_root_bounds hk h.1 h.2
  constructor
  · apply (div_le_iff₀ hR0).2
    simpa [mul_comm] using hb.1
  · apply (le_div_iff₀ hR0).2
    simpa [mul_comm] using hb.2

theorem flatTail_complexityScale_boundary {k : ℕ} (hk : 0 < k)
    {R : ℝ} (hR0 : 0 < R) (hR : R < 1 / 4) :
    complexityScale (flatTailLaw k hk R hR0.le (by linarith)) R =
      heavyRoot (flatTailLaw k hk R hR0.le (by linarith)) R := by
  rw [complexityScale, flatTailLaw_largestMass hk hR0.le (by linarith) hR.le]
  simp [show R ≠ 1 by linarith, show 1 - R ≠ 1 by linarith,
    show (3 : ℝ) / 4 < 1 - R by linarith]

theorem flatTail_complexityScale_exterior {k : ℕ} (hk : 0 < k)
    {R Δ : ℝ} (hR0 : 0 < R) (hR : R < 1 / 4) (hΔ : 0 < Δ) (he : R + Δ < 1) :
    complexityScale (flatTailLaw k hk R hR0.le (by linarith)) (R + Δ) =
      min (heavyRoot (flatTailLaw k hk R hR0.le (by linarith)) R)
        (R / Δ ^ 2 + 1 / Δ) := by
  rw [complexityScale, flatTailLaw_largestMass hk hR0.le (by linarith) hR.le]
  simp [show R + Δ ≠ 1 by linarith, show 1 - R ≠ 1 by linarith,
    show (3 : ℝ) / 4 < 1 - R by linarith, show ¬R + Δ ≤ R by linarith]

/-- The explicit exterior transition scale, with the exact count-test term
and the two-fifths boundary scale. The domain excludes ε=1, whose testing
problem is empty and is treated separately by the manuscript. -/
theorem flatTail_exterior_scale_bounds {k : ℕ} (hk : 0 < k)
    {R Δ : ℝ} (hR0 : 0 < R) (hR : R < 1 / 4) (hΔ : 0 < Δ) (he : R + Δ < 1) :
    let q := flatTailLaw k hk R hR0.le (by linarith)
    let S := min ((k : ℝ) ^ (2 / 5 : ℝ) / R) (R / Δ ^ 2 + 1 / Δ)
    S ≤ complexityScale q (R + Δ) ∧ complexityScale q (R + Δ) ≤ 64 * S := by
  have hb := flatTail_boundary_heavyRoot_bounds hk hR0 (by linarith) hR.le
  dsimp only
  rw [flatTail_complexityScale_exterior hk hR0 hR hΔ he]
  constructor
  · exact min_le_min_right _ hb.1
  · have hcount : 0 ≤ R / Δ ^ 2 + 1 / Δ := by positivity
    have hscale : heavyRoot (flatTailLaw k hk R hR0.le (by linarith)) R ≤
        64 * ((k : ℝ) ^ (2 / 5 : ℝ) / R) := by simpa [mul_div_assoc] using hb.2
    have h := min_le_min hscale (show R / Δ ^ 2 + 1 / Δ ≤ 64 * (R / Δ ^ 2 + 1 / Δ) by linarith)
    simpa only [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 64)] using h

/-- Boundary sample complexity for the concrete flat-tail reference. The
existing statistical theorem is used only after the instance scale is proved. -/
theorem flatTail_testing_characterization_boundary :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (k : ℕ) (hk : 0 < k) (R : ℝ) (hR0 : 0 < R) (hR : R < 1 / 4),
        let q := flatTailLaw k hk R hR0.le (by linarith)
        let S := (k : ℝ) ^ (2 / 5 : ℝ) / R
        (∀ n : ℕ, HasIdentityTest q R n → c * S ≤ n) ∧
        (∃ n : ℕ, HasIdentityTest q R n ∧ (n : ℝ) ≤ C * S) := by
  obtain ⟨c, C, hc, hcC, h⟩ := countable_characterization_realScale
  have hC := hc.trans hcC
  refine ⟨c, 64 * C, hc, by linarith, ?_⟩
  intro k hk R hR0 hR
  let q := flatTailLaw k hk R hR0.le (by linarith)
  obtain ⟨hl, hu⟩ := h q R hR0 (by linarith)
  have hb := flatTail_boundary_heavyRoot_bounds hk hR0 (by linarith) hR.le
  have heq := flatTail_complexityScale_boundary hk hR0 hR
  rw [heq] at hl hu
  constructor
  · intro n hn
    exact (mul_le_mul_of_nonneg_left hb.1 hc.le).trans (hl n hn)
  · obtain ⟨n, hn, hnle⟩ := hu
    refine ⟨n, hn, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hb.2 hC.le
    calc
      (n : ℝ) ≤ C * heavyRoot q R := hnle
      _ ≤ C * (64 * (k : ℝ) ^ (2 / 5 : ℝ) / R) := hm
      _ = (64 * C) * ((k : ℝ) ^ (2 / 5 : ℝ) / R) := by ring

/-- Exterior sample complexity with the two competing instance scales. -/
theorem flatTail_testing_characterization_exterior :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (k : ℕ) (hk : 0 < k) (R : ℝ) (hR0 : 0 < R) (hR : R < 1 / 4)
        (Δ : ℝ), 0 < Δ → R + Δ < 1 →
        let q := flatTailLaw k hk R hR0.le (by linarith)
        let S := min ((k : ℝ) ^ (2 / 5 : ℝ) / R) (R / Δ ^ 2 + 1 / Δ)
        (∀ n : ℕ, HasIdentityTest q (R + Δ) n → c * S ≤ n) ∧
        (∃ n : ℕ, HasIdentityTest q (R + Δ) n ∧ (n : ℝ) ≤ C * S) := by
  obtain ⟨c, C, hc, hcC, h⟩ := countable_characterization_realScale
  have hC := hc.trans hcC
  refine ⟨c, 64 * C, hc, by linarith, ?_⟩
  intro k hk R hR0 hR Δ hΔ he
  let q := flatTailLaw k hk R hR0.le (by linarith)
  obtain ⟨hl, hu⟩ := h q (R + Δ) (by linarith) he.le
  have hb := flatTail_exterior_scale_bounds hk hR0 hR hΔ he
  constructor
  · intro n hn
    exact (mul_le_mul_of_nonneg_left hb.1 hc.le).trans (hl n hn)
  · obtain ⟨n, hn, hnle⟩ := hu
    refine ⟨n, hn, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hb.2 hC.le
    calc
      (n : ℝ) ≤ C * complexityScale q (R + Δ) := hnle
      _ ≤ C * (64 * min ((k : ℝ) ^ (2 / 5 : ℝ) / R) (R / Δ ^ 2 + 1 / Δ)) := hm
      _ = _ := by ring

end IdentityTesting
