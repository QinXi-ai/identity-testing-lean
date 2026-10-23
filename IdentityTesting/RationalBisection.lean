import IdentityTesting.AllocationGeometry
import Mathlib.Data.Rat.Cast.Order

/-! Executable rational bisection and its exact interval invariant.
This module alone makes no polynomial bit-complexity claim. -/
namespace IdentityTesting.RationalComputation

def bisect (p : ℚ → ℚ) : ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, l, u => (l, u)
  | n + 1, l, u =>
    let m := (l + u) / 2
    if p m ≤ 0 then bisect p n m u else bisect p n l m

theorem bisect_width (p : ℚ → ℚ) (n : ℕ) (l u : ℚ) :
    (bisect p n l u).2 - (bisect p n l u).1 = (u - l) / 2 ^ n := by
  induction n generalizing l u with
  | zero => simp [bisect]
  | succ n ih =>
    simp only [bisect]
    split <;> rw [ih, pow_succ] <;> ring

theorem bisect_contains (p : ℚ → ℚ) (r : ℝ)
    (hsign : ∀ x : ℚ, 0 ≤ x → x ≤ 1 → (p x ≤ 0 ↔ (x : ℝ) ≤ r))
    (n : ℕ) (l u : ℚ) (hl : 0 ≤ l) (hu : u ≤ 1)
    (hlr : (l : ℝ) ≤ r) (hru : r ≤ (u : ℝ)) :
    0 ≤ (bisect p n l u).1 ∧ (bisect p n l u).2 ≤ 1 ∧
      ((bisect p n l u).1 : ℝ) ≤ r ∧ r ≤ ((bisect p n l u).2 : ℝ) := by
  induction n generalizing l u with
  | zero => exact ⟨hl, hu, hlr, hru⟩
  | succ n ih =>
    have hlu : l ≤ u := by exact_mod_cast hlr.trans hru
    have hm0 : 0 ≤ (l + u) / 2 := by linarith
    have hm1 : (l + u) / 2 ≤ 1 := by linarith
    simp only [bisect]
    split_ifs with hp
    · exact ih _ _ hm0 hu ((hsign _ hm0 hm1).mp hp) hru
    · have hm : r ≤ (((l + u) / 2 : ℚ) : ℝ) := le_of_lt (lt_of_not_ge
        (fun h => hp ((hsign _ hm0 hm1).mpr h)))
      exact ih _ _ hl hm1 hlr hm

def coordinatePolynomial (a β x : ℚ) : ℚ := a * x ^ 3 - β * (1 - x ^ 4) ^ 2

def coordinateInterval (a β : ℚ) (n : ℕ) : ℚ × ℚ :=
  bisect (coordinatePolynomial a β) n 0 1

theorem coordinatePolynomial_strictMono {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    StrictMonoOn (fun x : ℝ => a * x ^ 3 - β * (1 - x ^ 4) ^ 2) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have h3 : x ^ 3 < y ^ 3 := by gcongr; exact hx.1
  have h4 : x ^ 4 ≤ y ^ 4 := by gcongr; exact hx.1
  have hy4 : y ^ 4 ≤ (1 : ℝ) := by exact pow_le_one₀ hy.1 hy.2
  have hs : (1 - y ^ 4) ^ 2 ≤ (1 - x ^ 4) ^ 2 := by
    nlinarith only [h4, hy4, mul_nonneg (sub_nonneg.mpr h4)
      (show 0 ≤ 2 - x ^ 4 - y ^ 4 by linarith)]
  have hm₁ := mul_lt_mul_of_pos_left h3 ha
  have hm₂ := mul_le_mul_of_nonneg_left hs hβ.le
  linarith only [hm₁, hm₂]

theorem exists_unique_coordinate_root (a β : ℚ) (ha : 0 < a) (hβ : 0 < β) :
    ∃! r : ℝ, r ∈ Set.Icc 0 1 ∧
      (a : ℝ) * r ^ 3 = (β : ℝ) * (1 - r ^ 4) ^ 2 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  let f : ℝ → ℝ := fun x => (a : ℝ) * x ^ 3 - (β : ℝ) * (1 - x ^ 4) ^ 2
  have hf : Continuous f := by fun_prop
  have h0 : f 0 ≤ 0 := by dsimp only [f]; nlinarith
  have h1 : 0 ≤ f 1 := by dsimp only [f]; nlinarith
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ⟨h0, h1⟩
  refine ⟨r, ⟨hr, sub_eq_zero.mp hfr⟩, ?_⟩
  intro y hy
  apply (coordinatePolynomial_strictMono ha' hβ').injOn hy.1 hr
  change f y = f r
  rw [hfr]
  exact sub_eq_zero.mpr hy.2

theorem coordinateInterval_spec (a β : ℚ) (ha : 0 < a) (hβ : 0 < β) (n : ℕ) :
    ∃ r : ℝ, (0 < r ∧ r < 1) ∧
      (a : ℝ) * r ^ 3 = (β : ℝ) * (1 - r ^ 4) ^ 2 ∧
      0 ≤ (coordinateInterval a β n).1 ∧ (coordinateInterval a β n).2 ≤ 1 ∧
      ((coordinateInterval a β n).1 : ℝ) ≤ r ∧ r ≤ ((coordinateInterval a β n).2 : ℝ) ∧
      (coordinateInterval a β n).2 - (coordinateInterval a β n).1 = 1 / 2 ^ n := by
  obtain ⟨r, ⟨hr, heq⟩, _⟩ := exists_unique_coordinate_root a β ha hβ
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  have hr0 : 0 < r := by
    apply lt_of_le_of_ne hr.1
    intro h
    rw [← h] at heq
    norm_num at heq
    linarith
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hr.2
    intro h
    rw [h] at heq
    norm_num at heq
    linarith
  have hsign : ∀ x : ℚ, 0 ≤ x → x ≤ 1 →
      (coordinatePolynomial a β x ≤ 0 ↔ (x : ℝ) ≤ r) := by
    intro x hx0 hx1
    have hx : (x : ℝ) ∈ Set.Icc 0 1 := by
      exact ⟨by exact_mod_cast hx0, by exact_mod_cast hx1⟩
    have hcast : (coordinatePolynomial a β x : ℝ) =
        (a : ℝ) * (x : ℝ) ^ 3 - (β : ℝ) * (1 - (x : ℝ) ^ 4) ^ 2 := by
      simp only [coordinatePolynomial, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_one]
    have hm := coordinatePolynomial_strictMono ha' hβ'
    have hz : (a : ℝ) * r ^ 3 - (β : ℝ) * (1 - r ^ 4) ^ 2 = 0 := sub_eq_zero.mpr heq
    constructor
    · intro hp
      have hp' : (coordinatePolynomial a β x : ℝ) ≤ 0 := by exact_mod_cast hp
      by_contra h
      have hlt := hm hr hx (lt_of_not_ge h)
      dsimp only at hlt
      rw [hz, ← hcast] at hlt
      exact (not_lt_of_ge hp') hlt
    · intro h
      have hp' := hm.monotoneOn hx hr h
      rw [hz, ← hcast] at hp'
      exact_mod_cast hp'
  obtain ⟨hl, hu, hlr, hru⟩ := bisect_contains (coordinatePolynomial a β) r hsign n 0 1
    (by norm_num) (by norm_num) (by simpa using hr.1) (by simpa using hr.2)
  exact ⟨r, ⟨hr0, hr1⟩, heq, hl, hu, hlr, hru, by
    simpa only [coordinateInterval, sub_zero] using bisect_width (coordinatePolynomial a β) n 0 1⟩

end IdentityTesting.RationalComputation
