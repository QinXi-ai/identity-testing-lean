import IdentityTesting.RationalAllocationOracleInputs

namespace IdentityTesting.RationalComputation

def sqrtInitialUpper (a : ℚ) : ℚ := 2 ^ (Nat.ceil a).size

def sqrtInterval (a δ : ℚ) : ℚ × ℚ :=
  bisect (fun x => x ^ 2 - a) (oracleDyadicPrecision (sqrtInitialUpper a) δ)
    0 (sqrtInitialUpper a)

theorem sqrtInitialUpper_spec (a : ℚ) (ha : 0 ≤ a) :
    0 < sqrtInitialUpper a ∧ Real.sqrt (a : ℝ) ≤ (sqrtInitialUpper a : ℝ) := by
  have hU : (0 : ℚ) < sqrtInitialUpper a := by unfold sqrtInitialUpper; positivity
  have h1 : (1 : ℚ) ≤ sqrtInitialUpper a := by
    unfold sqrtInitialUpper
    exact one_le_pow₀ (by norm_num)
  have hceil : a ≤ (Nat.ceil a : ℚ) := Nat.le_ceil _
  have hlt : (Nat.ceil a : ℚ) < sqrtInitialUpper a := by
    unfold sqrtInitialUpper
    exact_mod_cast Nat.lt_size_self (Nat.ceil a)
  have haU : a ≤ sqrtInitialUpper a := hceil.trans hlt.le
  have hU' : (0 : ℝ) < sqrtInitialUpper a := by exact_mod_cast hU
  have h1' : (1 : ℝ) ≤ sqrtInitialUpper a := by exact_mod_cast h1
  have haU' : (a : ℝ) ≤ sqrtInitialUpper a := by exact_mod_cast haU
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ a by exact_mod_cast ha)
  refine ⟨hU, ?_⟩
  nlinarith [Real.sqrt_nonneg (a : ℝ)]

theorem sqrtBisect_contains (a : ℚ) (ha : 0 ≤ a) (n : ℕ) (l u : ℚ)
    (hl : 0 ≤ l) (hlr : (l : ℝ) ≤ Real.sqrt (a : ℝ))
    (hru : Real.sqrt (a : ℝ) ≤ (u : ℝ)) :
    0 ≤ (bisect (fun x => x ^ 2 - a) n l u).1 ∧
      ((bisect (fun x => x ^ 2 - a) n l u).1 : ℝ) ≤ Real.sqrt (a : ℝ) ∧
      Real.sqrt (a : ℝ) ≤ ((bisect (fun x => x ^ 2 - a) n l u).2 : ℝ) := by
  induction n generalizing l u with
  | zero => exact ⟨hl, hlr, hru⟩
  | succ n ih =>
    have hlu : l ≤ u := by exact_mod_cast hlr.trans hru
    have hm0 : 0 ≤ (l + u) / 2 := by linarith
    have hm0' : (0 : ℝ) ≤ (((l + u) / 2 : ℚ) : ℝ) := by exact_mod_cast hm0
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ a by exact_mod_cast ha)
    have hr0 := Real.sqrt_nonneg (a : ℝ)
    simp only [bisect]
    split_ifs with hp
    · have hp' : ((((l + u) / 2 : ℚ) : ℝ)) ^ 2 - (a : ℝ) ≤ 0 := by exact_mod_cast hp
      apply ih _ _ hm0 _ hru
      nlinarith
    · have hp' : 0 < ((((l + u) / 2 : ℚ) : ℝ)) ^ 2 - (a : ℝ) := by
        exact_mod_cast lt_of_not_ge hp
      apply ih _ _ hl hlr
      nlinarith

theorem sqrtInterval_spec (a δ : ℚ) (ha : 0 ≤ a) (hδ : 0 < δ) :
    0 ≤ (sqrtInterval a δ).1 ∧
      ((sqrtInterval a δ).1 : ℝ) ≤ Real.sqrt (a : ℝ) ∧
      Real.sqrt (a : ℝ) ≤ ((sqrtInterval a δ).2 : ℝ) ∧
      (sqrtInterval a δ).2 - (sqrtInterval a δ).1 ≤ δ := by
  obtain ⟨hl, hlr, hru⟩ := sqrtBisect_contains a ha
    (oracleDyadicPrecision (sqrtInitialUpper a) δ) 0 (sqrtInitialUpper a)
    (by norm_num) (by simpa using Real.sqrt_nonneg (a : ℝ)) (sqrtInitialUpper_spec a ha).2
  refine ⟨hl, hlr, hru, ?_⟩
  unfold sqrtInterval
  rw [bisect_width, sub_zero]
  exact oracleDyadicPrecision_spec _ _ hδ

def dyadicSqrtUpper (a : ℚ) : ℚ := (sqrtInterval a (min 1 a)).2

theorem min_one_le_sqrt (a : ℚ) (ha : 0 < a) :
    ((min 1 a : ℚ) : ℝ) ≤ Real.sqrt (a : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hs := Real.sq_sqrt ha'.le
  rw [Rat.cast_min, Rat.cast_one]
  by_cases h : (a : ℝ) ≤ 1
  · rw [min_eq_right h]
    nlinarith [Real.sqrt_nonneg (a : ℝ)]
  · rw [min_eq_left (le_of_not_ge h)]
    nlinarith [Real.sqrt_nonneg (a : ℝ)]

theorem dyadicSqrtUpper_spec (a : ℚ) (ha : 0 < a) :
    0 < dyadicSqrtUpper a ∧ Real.sqrt (a : ℝ) ≤ (dyadicSqrtUpper a : ℝ) ∧
      (dyadicSqrtUpper a : ℝ) ≤ 2 * Real.sqrt (a : ℝ) := by
  have hδ : (0 : ℚ) < min 1 a := lt_min (by norm_num) ha
  obtain ⟨hl, hlr, hru, hw⟩ := sqrtInterval_spec a (min 1 a) ha.le hδ
  have hw' : ((sqrtInterval a (min 1 a)).2 : ℝ) - ((sqrtInterval a (min 1 a)).1 : ℝ) ≤
      ((min 1 a : ℚ) : ℝ) := by exact_mod_cast hw
  have hr0 := Real.sqrt_pos.mpr (show (0 : ℝ) < a by exact_mod_cast ha)
  refine ⟨?_, hru, ?_⟩
  · exact_mod_cast hr0.trans_le hru
  · dsimp only [dyadicSqrtUpper]
    linarith [min_one_le_sqrt a ha]

theorem sqrtInterval_precision_le (a δ : ℚ) (m : ℕ)
    (h : sqrtInitialUpper a / δ ≤ 2 ^ m) :
    oracleDyadicPrecision (sqrtInitialUpper a) δ ≤ m + 1 :=
  oracleDyadicPrecision_le _ _ _ h

theorem sqrtInitialUpper_le_pow (a : ℚ) (m : ℕ) (ha : a ≤ 2 ^ m) :
    sqrtInitialUpper a ≤ 2 ^ (m + 1) := by
  have hc : Nat.ceil a ≤ 2 ^ m := Nat.ceil_le.mpr (by exact_mod_cast ha)
  have hs : (Nat.ceil a).size ≤ m + 1 := by
    simpa only [Nat.size_pow] using Nat.size_le_size hc
  unfold sqrtInitialUpper
  exact pow_le_pow_right₀ (by norm_num) hs

theorem sqrtInterval_precision_le_of_bounds (a δ : ℚ) (m c : ℕ)
    (ha : a ≤ 2 ^ m) (hδ : 0 < δ) (hrec : 1 / δ ≤ 2 ^ c) :
    oracleDyadicPrecision (sqrtInitialUpper a) δ ≤ m + c + 2 := by
  have h := mul_le_mul (sqrtInitialUpper_le_pow a m ha) hrec
    (one_div_pos.mpr hδ).le (by positivity : (0 : ℚ) ≤ 2 ^ (m + 1))
  have hbound : sqrtInitialUpper a / δ ≤ 2 ^ (m + c + 1) := by
    convert h using 1 <;> (try simp only [pow_add]) <;> ring
  exact oracleDyadicPrecision_le _ _ (m + c + 1) hbound

def IsDyadic (x : ℚ) : Prop := ∃ z : ℤ, ∃ n : ℕ, x = z / 2 ^ n

theorem IsDyadic.midpoint {l u : ℚ} (hl : IsDyadic l) (hu : IsDyadic u) :
    IsDyadic ((l + u) / 2) := by
  obtain ⟨z, m, rfl⟩ := hl
  obtain ⟨w, n, rfl⟩ := hu
  refine ⟨z * 2 ^ n + w * 2 ^ m, m + n + 1, ?_⟩
  push_cast
  rw [pow_add, pow_add]
  field_simp
  <;> ring

theorem bisect_dyadic (p : ℚ → ℚ) (n : ℕ) (l u : ℚ)
    (hl : IsDyadic l) (hu : IsDyadic u) :
    IsDyadic (bisect p n l u).1 ∧ IsDyadic (bisect p n l u).2 := by
  induction n generalizing l u with
  | zero => exact ⟨hl, hu⟩
  | succ n ih =>
    simp only [bisect]
    split_ifs
    · exact ih _ _ (hl.midpoint hu) hu
    · exact ih _ _ hl (hl.midpoint hu)

theorem sqrtInterval_dyadic (a δ : ℚ) :
    IsDyadic (sqrtInterval a δ).1 ∧ IsDyadic (sqrtInterval a δ).2 := by
  apply bisect_dyadic
  · exact ⟨0, 0, by norm_num⟩
  · exact ⟨2 ^ (Nat.ceil a).size, 0, by simp [sqrtInitialUpper]⟩

theorem dyadicSqrtUpper_dyadic (a : ℚ) : IsDyadic (dyadicSqrtUpper a) :=
  (sqrtInterval_dyadic a (min 1 a)).2

end IdentityTesting.RationalComputation
