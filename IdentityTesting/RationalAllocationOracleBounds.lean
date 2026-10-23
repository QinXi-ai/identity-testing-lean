import IdentityTesting.RationalAllocationOracleScalar

/-! # Explicit parameter bounds and the actual original optimizer -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation

def oracleBetaLower {k : ℕ} (a : Fin k → ℚ) (t : ℚ) : ℚ :=
  1 / (t ^ 2 * ∑ i, a i)

def oracleBetaUpper (a₀ t : ℚ) : ℚ :=
  (1 + t ^ 2 * a₀ ^ 2) ^ 2 / (t ^ 4 * a₀ ^ 3)

def oracleAtomLower {k : ℕ} (a : Fin k → ℚ) : ℚ := 1 / (∑ i, 1 / a i)

def oraclePoleGap (aLower betaUpper : ℚ) : ℚ := min (1 / 2) (aLower / (128 * betaUpper))

theorem stationary_beta_upper {t a β x : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hβ : 0 < β) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) (hcost : allocationCost t a x ≤ 1) :
    β ≤ (1 + t ^ 2 * a ^ 2) ^ 2 / (t ^ 4 * a ^ 3) := by
  let c := t ^ 2 * a ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : 0 < 1 - x ^ 4 := sub_pos.mpr (allocation_fourth_lt_one hx0 hx1)
  have hraw : c * x ^ 4 ≤ 1 - x ^ 4 := by
    exact (div_le_one hd).mp hcost
  have hsep : c ≤ (1 + c) * (1 - x ^ 4) := by nlinarith only [hraw]
  have hsep2 := pow_le_pow_left₀ hc.le hsep 2
  have hβsep := mul_le_mul_of_nonneg_left hsep2 hβ.le
  have hx3 : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1.le
  have hax3 := mul_le_mul_of_nonneg_left hx3 ha.le
  have hax := mul_le_mul_of_nonneg_left hax3 (sq_nonneg (1 + c))
  have hbig : β * c ^ 2 ≤ a * (1 + c) ^ 2 := by
    calc
      _ ≤ β * ((1 + c) * (1 - x ^ 4)) ^ 2 := hβsep
      _ = (1 + c) ^ 2 * (a * x ^ 3) := by rw [hx]; ring
      _ ≤ a * (1 + c) ^ 2 := by nlinarith only [hax]
  apply (le_div_iff₀ (by positivity : 0 < t ^ 4 * a ^ 3)).2
  have hcancel : a * (β * (t ^ 4 * a ^ 3)) ≤ a * (1 + t ^ 2 * a ^ 2) ^ 2 := by
    convert hbig using 1; dsimp only [c]; ring
  exact (mul_le_mul_iff_right₀ ha).mp hcancel

theorem stationary_beta_lower {k : ℕ} {a x : Fin k → ℝ} {t β : ℝ}
    (ht : 0 < t) (ha : ∀ i, 0 < a i) (hβ : 0 < β)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1) (hr : 0 < ∑ i, a i)
    (hbudget : 1 = t ^ 2 * β * ∑ i, a i * x i * (1 - (x i) ^ 4)) :
    1 / (t ^ 2 * ∑ i, a i) ≤ β := by
  have hsum : (∑ i, a i * x i * (1 - (x i) ^ 4)) ≤ ∑ i, a i := by
    apply Finset.sum_le_sum
    intro i _
    have hdef : 0 ≤ 1 - (x i) ^ 4 := (sub_pos.mpr (allocation_fourth_lt_one (hx i).1 (hx i).2)).le
    have hxi := mul_le_mul_of_nonneg_left (hx i).2.le (ha i).le
    have hfactor := mul_le_mul_of_nonneg_left (show 1 - (x i) ^ 4 ≤ 1 by linarith only [pow_nonneg (hx i).1 4])
      (mul_nonneg (ha i).le (hx i).1)
    nlinarith only [hfactor, hxi]
  have h := mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg t) hβ.le)
  rw [← hbudget] at h
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos ht) hr)).2
  nlinarith only [h]

theorem stationary_coordinate_pole_gap {aLower B ρ a β x : ℝ}
    (hmin : 0 < aLower) (ha : aLower ≤ a) (hβ : 0 < β) (hB : β ≤ B)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ (1 : ℝ) / 2) (hρsize : 128 * B * ρ ≤ aLower)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hx : a * x ^ 3 = β * (1 - x ^ 4) ^ 2) : x ≤ 1 - ρ := by
  have ha0 : 0 < a := hmin.trans_le ha
  have hB0 : 0 < B := hβ.trans_le hB
  by_contra hnot
  have hxhalf : (1 : ℝ) / 2 ≤ x := by linarith only [lt_of_not_ge hnot, hρhalf]
  have hx3 : (1 : ℝ) / 8 ≤ x ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hxhalf 3
    norm_num at h
    exact h
  have hleft : aLower / 8 ≤ a * x ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hx3 ha0.le
    nlinarith only [h, ha]
  have hdef : 1 - x ^ 4 ≤ 4 * (1 - x) := by
    simpa using (fourth_difference_bounds hx0 hx1.le (le_refl (1 : ℝ))).2
  have hdef0 : 0 ≤ 1 - x ^ 4 := (sub_pos.mpr (allocation_fourth_lt_one hx0 hx1)).le
  have hdefsq := pow_le_pow_left₀ hdef0 hdef 2
  have hδ : (1 - x) ^ 2 ≤ 1 - x := pow_le_of_le_one (by linarith only [hx1]) (by linarith only [hx0]) (by norm_num : (2 : ℕ) ≠ 0)
  have hright : a * x ^ 3 ≤ 16 * B * (1 - x) := by
    rw [hx]
    calc
      _ ≤ B * (1 - x ^ 4) ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ ≤ B * (4 * (1 - x)) ^ 2 := mul_le_mul_of_nonneg_left hdefsq hB0.le
      _ ≤ 16 * B * (1 - x) := by
        have h := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 16 * B)
        nlinarith only [h]
  have hstrict : 16 * B * (1 - x) < 16 * B * ρ :=
    mul_lt_mul_of_pos_left (by linarith only [lt_of_not_ge hnot]) (by positivity)
  linarith only [hleft, hright, hstrict, hρsize]

theorem exists_actual_oracle_optimizer {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℝ) (t : ℝ) (ha : ∀ i, 0 < a i) (ht : 0 < t) (j : Fin k) :
    ∃ (x : Fin k → ℝ) (β : ℝ), (∀ i, 0 < x i ∧ x i < 1) ∧ 0 < β ∧
      (∀ i, a i * (x i) ^ 3 = β * (1 - (x i) ^ 4) ^ 2) ∧
      (∑ i, allocationCost t (a i) (x i)) = 1 ∧
      allocationD (extendFiniteVector a) t = ∑ i, a i * x i ∧
      1 / (t ^ 2 * ∑ i, a i) ≤ β ∧ β ≤ (1 + t ^ 2 * (a j) ^ 2) ^ 2 / (t ^ 4 * (a j) ^ 3) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer ht ha
  obtain ⟨β, hβ, hstationary, hbudget⟩ := allocation_optimizer_kkt ht ha hu0 hu1 hmax
  let x : Fin k → ℝ := fun i => allocationCoordinate t (a i) (u i)
  have hx : ∀ i, 0 < x i ∧ x i < 1 := fun i =>
    ⟨allocationCoordinate_pos ht (ha i) (hu0 i), (allocationCoordinate_range ht (ha i) (hu0 i).le).2⟩
  have hcost : ∀ i, allocationCost t (a i) (x i) = u i := fun i =>
    allocationCost_coordinate ht (ha i) (hu0 i).le
  have hr : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have huj : u j ≤ 1 := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => (hu0 i).le) (Finset.mem_univ j)
    rwa [hu1] at h
  refine ⟨x, β, hx, hβ, hstationary, ?_, ?_, ?_, ?_⟩
  · simp_rw [hcost]
    exact hu1
  · exact allocationD_extendFiniteVector_eq_optimizer ht ha ⟨fun i => (hu0 i).le, hu1.le⟩ hmax
  · exact stationary_beta_lower ht ha hβ (fun i => ⟨(hx i).1.le, (hx i).2⟩) hr hbudget
  · exact stationary_beta_upper ht (ha j) hβ (hx j).1.le (hx j).2 (hstationary j)
      (by rw [hcost]; exact huj)

end IdentityTesting.RationalComputation
