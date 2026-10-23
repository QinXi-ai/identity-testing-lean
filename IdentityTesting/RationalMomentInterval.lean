import IdentityTesting.RationalSqrtInterval
import IdentityTesting.FiniteOverlapMoment

open scoped BigOperators
namespace IdentityTesting.RationalComputation

def rationalMomentUpper {k : ℕ} (q : Fin k → ℚ) (δ : ℚ) : ℚ :=
  ∑ i, min (q i) (q i * dyadicSqrtUpper (q i / δ))

def rationalMomentInterval {k : ℕ} (q : Fin k → ℚ) (δ : ℚ) : ℚ × ℚ :=
  (1 / rationalMomentUpper q δ, 2 / rationalMomentUpper q δ)

noncomputable def rationalFiniteLaw {k : ℕ} (q : Fin k → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i = 1) : FiniteTesting.Probability (Fin k) where
  mass i := q i
  nonneg i := by exact_mod_cast hq i
  total := by exact_mod_cast hs

theorem rationalMomentUpper_compare {k : ℕ} (q : Fin k → ℚ) (δ : ℚ)
    (hq : ∀ i, 0 < q i) (hδ : 0 < δ) :
    (∑ i, min (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ)))) ≤
        (rationalMomentUpper q δ : ℝ) ∧
      (rationalMomentUpper q δ : ℝ) ≤
        2 * ∑ i, min (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ))) := by
  have hterm (i : Fin k) :
      min (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ))) ≤
        ((min (q i) (q i * dyadicSqrtUpper (q i / δ)) : ℚ) : ℝ) ∧
      ((min (q i) (q i * dyadicSqrtUpper (q i / δ)) : ℚ) : ℝ) ≤
        2 * min (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ))) := by
    have hqi : (0 : ℝ) < q i := by exact_mod_cast hq i
    obtain ⟨_, hl, hu⟩ := dyadicSqrtUpper_spec (q i / δ) (div_pos (hq i) hδ)
    rw [Rat.cast_div] at hl hu
    simp only [Rat.cast_min, Rat.cast_mul]
    constructor
    · exact min_le_min le_rfl (mul_le_mul_of_nonneg_left hl hqi.le)
    · rcases le_total (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ))) with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h]
        have hm := mul_le_mul_of_nonneg_left hu hqi.le
        exact (min_le_right _ _).trans (by nlinarith only [hm])
  simp only [rationalMomentUpper, Rat.cast_sum]
  constructor
  · exact Finset.sum_le_sum (fun i _ => (hterm i).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hterm i).2)

theorem rationalMomentUpper_overlap {k : ℕ} (q : Fin k → ℚ) (δ : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hδ : 0 < δ) :
    let p := rationalFiniteLaw q (fun i => (hq i).le) hs
    overlapMoment (extendFiniteLaw p) δ ≤ (rationalMomentUpper q δ : ℝ) ∧
      (rationalMomentUpper q δ : ℝ) ≤ 2 * overlapMoment (extendFiniteLaw p) δ := by
  dsimp only
  rw [overlapMoment_extendFiniteLaw]
  have hid : finiteOverlapMoment (rationalFiniteLaw q (fun i => (hq i).le) hs) δ =
      ∑ i, min (q i : ℝ) ((q i : ℝ) * Real.sqrt ((q i : ℝ) / (δ : ℝ))) := by
    unfold finiteOverlapMoment
    apply Finset.sum_congr rfl
    intro i _
    change min (q i : ℝ) ((q i : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (δ : ℝ)) = _
    rw [allocation_three_halves_eq (show (0 : ℝ) ≤ q i by exact_mod_cast (hq i).le),
      Real.sqrt_div (show (0 : ℝ) ≤ q i by exact_mod_cast (hq i).le)]
    congr 1
    ring
  rw [hid]
  exact rationalMomentUpper_compare q δ hq hδ

theorem rationalMomentInterval_spec {k : ℕ} (q : Fin k → ℚ) (δ : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hδ : 0 < δ) :
    let p := rationalFiniteLaw q (fun i => (hq i).le) hs
    0 < (rationalMomentInterval q δ).1 ∧
      ((rationalMomentInterval q δ).1 : ℝ) ≤ 1 / overlapMoment (extendFiniteLaw p) δ ∧
      1 / overlapMoment (extendFiniteLaw p) δ ≤ ((rationalMomentInterval q δ).2 : ℝ) ∧
      (rationalMomentInterval q δ).2 = 2 * (rationalMomentInterval q δ).1 := by
  dsimp only
  let p := rationalFiniteLaw q (fun i => (hq i).le) hs
  have hW : 0 < overlapMoment (extendFiniteLaw p) δ :=
    overlapMoment_pos _ (by exact_mod_cast hδ)
  obtain ⟨hl, hu⟩ := rationalMomentUpper_overlap q δ hq hs hδ
  have hWt : (0 : ℝ) < rationalMomentUpper q δ := hW.trans_le hl
  have hWtq : 0 < rationalMomentUpper q δ := by exact_mod_cast hWt
  refine ⟨one_div_pos.mpr hWtq, ?_, ?_, ?_⟩
  · simp only [rationalMomentInterval, Rat.cast_div, Rat.cast_one]
    exact one_div_le_one_div_of_le hW hl
  · simp only [rationalMomentInterval, Rat.cast_div, Rat.cast_ofNat]
    apply (div_le_div_iff₀ hW hWt).2
    simpa only [one_mul] using hu
  · dsimp only [rationalMomentInterval]
    ring

end IdentityTesting.RationalComputation
