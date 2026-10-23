import IdentityTesting.RationalAllocationOracleCoordinates
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor

/-! Actual positive rational inputs discharge all coordinate pole hypotheses. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

theorem oracleBetaLower_pos {k : ℕ} [Nonempty (Fin k)] (a : Fin k → ℚ)
    (t : ℚ) (ha : ∀ i, 0 < a i) (ht : 0 < t) : 0 < oracleBetaLower a t := by
  have hs : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  unfold oracleBetaLower
  positivity

theorem oracleBetaUpper_pos {a₀ t : ℚ} (ha : 0 < a₀) (ht : 0 < t) :
    0 < oracleBetaUpper a₀ t := by
  unfold oracleBetaUpper
  positivity

theorem oracleAtomLower_pos {k : ℕ} [Nonempty (Fin k)] (a : Fin k → ℚ)
    (ha : ∀ i, 0 < a i) : 0 < oracleAtomLower a := by
  unfold oracleAtomLower
  exact one_div_pos.mpr (Finset.sum_pos (fun i _ => one_div_pos.mpr (ha i)) Finset.univ_nonempty)

theorem oracleAtomLower_le {k : ℕ} (a : Fin k → ℚ)
    (ha : ∀ i, 0 < a i) (i : Fin k) : oracleAtomLower a ≤ a i := by
  have hs : 1 / a i ≤ ∑ j, 1 / a j :=
    Finset.single_le_sum (fun j _ => (one_div_pos.mpr (ha j)).le) (Finset.mem_univ i)
  have hp : 0 < ∑ j, 1 / a j := (one_div_pos.mpr (ha i)).trans_le hs
  unfold oracleAtomLower
  apply (div_le_iff₀ hp).2
  have hh := mul_le_mul_of_nonneg_left hs (ha i).le
  simpa [ne_of_gt (ha i)] using hh

theorem oraclePoleGap_spec {aLower B : ℚ} (ha : 0 < aLower) (hB : 0 < B) :
    0 < oraclePoleGap aLower B ∧ oraclePoleGap aLower B ≤ 1 / 2 ∧
      128 * B * oraclePoleGap aLower B ≤ aLower := by
  have hden : 0 < 128 * B := by positivity
  refine ⟨lt_min (by norm_num) (div_pos ha hden), min_le_left _ _, ?_⟩
  have h := min_le_right (1 / 2 : ℚ) (aLower / (128 * B))
  simpa [oraclePoleGap, mul_comm] using (le_div_iff₀ hden).mp h

theorem oracleCoordinate_pole_actual {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℚ) (β B : ℚ) (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hB : β ≤ B)
    (i : Fin k) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hxeq : (a i : ℝ) * x ^ 3 = (β : ℝ) * (1 - x ^ 4) ^ 2) :
    x ≤ 1 - (oraclePoleGap (oracleAtomLower a) B : ℝ) := by
  have hmin := oracleAtomLower_pos a ha
  have hρ := oraclePoleGap_spec hmin (hβ.trans_le hB)
  apply stationary_coordinate_pole_gap
    (aLower := (oracleAtomLower a : ℝ)) (B := (B : ℝ))
    (by exact_mod_cast hmin) (by exact_mod_cast oracleAtomLower_le a ha i)
    (by exact_mod_cast hβ) (by exact_mod_cast hB)
    (by exact_mod_cast hρ.1) (by
      have hh := Rat.cast_le (K := ℝ) |>.mpr hρ.2.1
      norm_num at hh
      exact hh)
    (by exact_mod_cast hρ.2.2) hx0 hx1 hxeq

theorem oracleEvaluation_contains_actual {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℚ) (t β B : ℚ) (ha : ∀ i, 0 < a i) (hβ : 0 < β)
    (hB : β ≤ B) (n : ℕ) (x : Fin k → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hstationary : ∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2) :
    let ρ := oraclePoleGap (oracleAtomLower a) B
    ((oracleBudgetInterval a t β ρ n).1 : ℝ) ≤ ∑ i, allocationCost t (a i) (x i) ∧
      (∑ i, allocationCost t (a i) (x i)) ≤ ((oracleBudgetInterval a t β ρ n).2 : ℝ) ∧
      ((oracleObjectiveInterval a β ρ n).1 : ℝ) ≤ ∑ i, (a i : ℝ) * x i ∧
      (∑ i, (a i : ℝ) * x i) ≤ ((oracleObjectiveInterval a β ρ n).2 : ℝ) := by
  apply oracleEvaluation_contains a t β _ ha hβ
    (oraclePoleGap_spec (oracleAtomLower_pos a ha) (hβ.trans_le hB)).1 n x hx hstationary
  exact fun i => oracleCoordinate_pole_actual a β B ha hβ hB i (hx i).1.le (hx i).2 (hstationary i)

theorem exists_actual_coordinate_vector {k : ℕ} (a : Fin k → ℚ) (β : ℚ)
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) :
    ∃ x : Fin k → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
      (∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2) := by
  have h : ∀ i, ∃ x : ℝ, (0 < x ∧ x < 1) ∧
      (a i : ℝ) * x ^ 3 = (β : ℝ) * (1 - x ^ 4) ^ 2 := by
    intro i
    obtain ⟨x, hx, heq, _⟩ := coordinateInterval_spec (a i) β (ha i) hβ 0
    exact ⟨x, hx, heq⟩
  choose x hx heq using h
  exact ⟨x, hx, heq⟩

theorem oracleBudgetInterval_width {k : ℕ} (a : Fin k → ℚ) (t β ρ : ℚ)
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hρ : 0 < ρ) (n : ℕ)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hstationary : ∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2)
    (hpole : ∀ i, x i ≤ 1 - (ρ : ℝ)) :
    (oracleBudgetInterval a t β ρ n).2 - (oracleBudgetInterval a t β ρ n).1 ≤
      (4 * k * t ^ 2 * (∑ i, a i) ^ 2 / ρ ^ 2) / 2 ^ n := by
  have heach (i : Fin k) :
      rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).2 -
        rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).1 ≤
      (4 * t ^ 2 * (∑ j, a j) ^ 2 / ρ ^ 2) / 2 ^ n := by
    have hI := oracleCoordinateInterval_spec (a i) β ρ (ha i) hβ n
      (hx i).1 (hx i).2 (hstationary i) (hpole i)
    have hlu : (oracleCoordinateInterval (a i) β ρ n).1 ≤
        (oracleCoordinateInterval (a i) β ρ n).2 := by
      exact_mod_cast hI.2.2.1.trans hI.2.2.2.1
    have hcost := allocationCost_lipschitz (t := (t : ℝ)) (a := (a i : ℝ))
      (l := ((oracleCoordinateInterval (a i) β ρ n).1 : ℝ))
      (u := ((oracleCoordinateInterval (a i) β ρ n).2 : ℝ)) (ρ := (ρ : ℝ))
      (by exact_mod_cast hI.1) (by exact_mod_cast hlu) (by exact_mod_cast hρ)
      (by exact_mod_cast hI.2.1)
    have hcostq :
        rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).2 -
          rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).1 ≤
        (4 * t ^ 2 * (a i) ^ 2 / ρ ^ 2) *
          ((oracleCoordinateInterval (a i) β ρ n).2 - (oracleCoordinateInterval (a i) β ρ n).1) := by
      rw [← rationalAllocationCost_cast, ← rationalAllocationCost_cast] at hcost
      exact_mod_cast hcost
    have hai : a i ≤ ∑ j, a j :=
      Finset.single_le_sum (fun j _ => (ha j).le) (Finset.mem_univ i)
    have hsq := pow_le_pow_left₀ (ha i).le hai 2
    have hc : 4 * t ^ 2 * (a i) ^ 2 / ρ ^ 2 ≤ 4 * t ^ 2 * (∑ j, a j) ^ 2 / ρ ^ 2 := by
      gcongr
    calc
      _ ≤ (4 * t ^ 2 * (a i) ^ 2 / ρ ^ 2) *
          ((oracleCoordinateInterval (a i) β ρ n).2 - (oracleCoordinateInterval (a i) β ρ n).1) := hcostq
      _ ≤ (4 * t ^ 2 * (∑ j, a j) ^ 2 / ρ ^ 2) * (1 / 2 ^ n) :=
        mul_le_mul hc hI.2.2.2.2 (sub_nonneg.mpr hlu) (by positivity)
      _ = _ := by ring
  simp only [oracleBudgetInterval]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _i : Fin k, (4 * t ^ 2 * (∑ j, a j) ^ 2 / ρ ^ 2) / 2 ^ n :=
      Finset.sum_le_sum (fun i _ => heach i)
    _ = _ := by simp; ring

/-- Binary precision: the bit length of a rational ceiling, not unary reciprocal fuel. -/
def oracleDyadicPrecision (C δ : ℚ) : ℕ := (Nat.ceil (C / δ)).size

theorem oracleDyadicPrecision_spec (C δ : ℚ) (hδ : 0 < δ) :
    C / 2 ^ oracleDyadicPrecision C δ ≤ δ := by
  have hceil : C / δ ≤ (Nat.ceil (C / δ) : ℚ) := Nat.le_ceil _
  have hsize : (Nat.ceil (C / δ) : ℚ) < 2 ^ oracleDyadicPrecision C δ := by
    exact_mod_cast Nat.lt_size_self (Nat.ceil (C / δ))
  have hc := (div_le_iff₀ hδ).mp (hceil.trans hsize.le)
  exact (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ oracleDyadicPrecision C δ)).2
    (by nlinarith only [hc])

theorem oracleDyadicPrecision_le (C δ : ℚ) (m : ℕ) (h : C / δ ≤ 2 ^ m) :
    oracleDyadicPrecision C δ ≤ m + 1 := by
  have hc : Nat.ceil (C / δ) ≤ 2 ^ m := Nat.ceil_le.mpr (by exact_mod_cast h)
  have hs := Nat.size_le_size hc
  simpa only [oracleDyadicPrecision, Nat.size_pow] using hs

theorem oracleEvaluation_exists_actual {k : ℕ} [Nonempty (Fin k)]
    (a : Fin k → ℚ) (t β B : ℚ) (ha : ∀ i, 0 < a i) (hβ : 0 < β)
    (hB : β ≤ B) (n : ℕ) :
    let ρ := oraclePoleGap (oracleAtomLower a) B
    ∃ x : Fin k → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
      (∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2) ∧
      ((oracleBudgetInterval a t β ρ n).1 : ℝ) ≤ ∑ i, allocationCost t (a i) (x i) ∧
      (∑ i, allocationCost t (a i) (x i)) ≤ ((oracleBudgetInterval a t β ρ n).2 : ℝ) ∧
      ((oracleObjectiveInterval a β ρ n).1 : ℝ) ≤ ∑ i, (a i : ℝ) * x i ∧
      (∑ i, (a i : ℝ) * x i) ≤ ((oracleObjectiveInterval a β ρ n).2 : ℝ) ∧
      (oracleBudgetInterval a t β ρ n).2 - (oracleBudgetInterval a t β ρ n).1 ≤
        (4 * k * t ^ 2 * (∑ i, a i) ^ 2 / ρ ^ 2) / 2 ^ n ∧
      (oracleObjectiveInterval a β ρ n).2 - (oracleObjectiveInterval a β ρ n).1 ≤
        (∑ i, a i) / 2 ^ n := by
  dsimp only
  obtain ⟨x, hx, heq⟩ := exists_actual_coordinate_vector a β ha hβ
  have hp := fun i => oracleCoordinate_pole_actual a β B ha hβ hB i (hx i).1.le (hx i).2 (heq i)
  have hρ := (oraclePoleGap_spec (oracleAtomLower_pos a ha) (hβ.trans_le hB)).1
  obtain ⟨hbl, hbu, hol, hou⟩ := oracleEvaluation_contains_actual a t β B ha hβ hB n x hx heq
  exact ⟨x, hx, heq, hbl, hbu, hol, hou,
    oracleBudgetInterval_width a t β _ ha hβ hρ n x hx heq hp,
    oracleObjectiveInterval_width a β _ ha hβ n x hx heq hp⟩

end IdentityTesting.RationalComputation
