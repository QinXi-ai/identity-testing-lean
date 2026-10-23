import IdentityTesting.RationalAllocationOracleBounds

/-! # Executable pole-safe rational coordinate and sum intervals -/

open scoped BigOperators
namespace IdentityTesting.RationalComputation

def rationalAllocationCost (t a x : ℚ) : ℚ := t ^ 2 * a ^ 2 * x ^ 4 / (1 - x ^ 4)

def oracleCoordinateInterval (a β ρ : ℚ) (n : ℕ) : ℚ × ℚ :=
  let I := coordinateInterval a β n
  (I.1, min I.2 (1 - ρ))

def oracleBudgetInterval {k : ℕ} (a : Fin k → ℚ) (t β ρ : ℚ) (n : ℕ) : ℚ × ℚ :=
  (∑ i, rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).1,
    ∑ i, rationalAllocationCost t (a i) (oracleCoordinateInterval (a i) β ρ n).2)

def oracleObjectiveInterval {k : ℕ} (a : Fin k → ℚ) (β ρ : ℚ) (n : ℕ) : ℚ × ℚ :=
  (∑ i, a i * (oracleCoordinateInterval (a i) β ρ n).1,
    ∑ i, a i * (oracleCoordinateInterval (a i) β ρ n).2)

theorem rationalAllocationCost_cast (t a x : ℚ) :
    (rationalAllocationCost t a x : ℝ) = allocationCost t a x := by
  simp only [rationalAllocationCost, allocationCost, Rat.cast_div, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_sub, Rat.cast_one]

theorem oracleCoordinateInterval_spec (a β ρ : ℚ) (ha : 0 < a) (hβ : 0 < β)
    (n : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hxeq : (a : ℝ) * x ^ 3 = (β : ℝ) * (1 - x ^ 4) ^ 2)
    (hpole : x ≤ 1 - (ρ : ℝ)) :
    0 ≤ (oracleCoordinateInterval a β ρ n).1 ∧
      (oracleCoordinateInterval a β ρ n).2 ≤ 1 - ρ ∧
      ((oracleCoordinateInterval a β ρ n).1 : ℝ) ≤ x ∧
      x ≤ ((oracleCoordinateInterval a β ρ n).2 : ℝ) ∧
      (oracleCoordinateInterval a β ρ n).2 - (oracleCoordinateInterval a β ρ n).1 ≤ 1 / 2 ^ n := by
  obtain ⟨r, hr, heq, hl, hu, hlr, hru, hwidth⟩ := coordinateInterval_spec a β ha hβ n
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ' : (0 : ℝ) < β := by exact_mod_cast hβ
  have hxr : x = r := by
    apply (coordinatePolynomial_strictMono ha' hβ').injOn ⟨hx0.le, hx1.le⟩ ⟨hr.1.le, hr.2.le⟩
    linarith only [hxeq, heq]
  rw [← hxr] at hlr hru
  refine ⟨hl, min_le_right _ _, hlr, ?_, ?_⟩
  · change x ≤ ((min (coordinateInterval a β n).2 (1 - ρ) : ℚ) : ℝ)
    rw [Rat.cast_min, Rat.cast_sub, Rat.cast_one]
    exact le_min hru hpole
  · change min (coordinateInterval a β n).2 (1 - ρ) - (coordinateInterval a β n).1 ≤ _
    linarith only [min_le_left (coordinateInterval a β n).2 (1 - ρ), hwidth]

theorem oracleEvaluation_contains {k : ℕ} (a : Fin k → ℚ) (t β ρ : ℚ)
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (hρ : 0 < ρ) (n : ℕ)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hstationary : ∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2)
    (hpole : ∀ i, x i ≤ 1 - (ρ : ℝ)) :
    ((oracleBudgetInterval a t β ρ n).1 : ℝ) ≤ ∑ i, allocationCost t (a i) (x i) ∧
      (∑ i, allocationCost t (a i) (x i)) ≤ ((oracleBudgetInterval a t β ρ n).2 : ℝ) ∧
      ((oracleObjectiveInterval a β ρ n).1 : ℝ) ≤ ∑ i, (a i : ℝ) * x i ∧
      (∑ i, (a i : ℝ) * x i) ≤ ((oracleObjectiveInterval a β ρ n).2 : ℝ) := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hI i := oracleCoordinateInterval_spec (a i) β ρ (ha i) hβ n (hx i).1 (hx i).2
    (hstationary i) (hpole i)
  have hl i : (0 : ℝ) ≤ (oracleCoordinateInterval (a i) β ρ n).1 := by exact_mod_cast (hI i).1
  have hu i : ((oracleCoordinateInterval (a i) β ρ n).2 : ℝ) < 1 := by
    have h := (hI i).2.1
    have h' : ((oracleCoordinateInterval (a i) β ρ n).2 : ℝ) ≤ 1 - (ρ : ℝ) := by exact_mod_cast h
    linarith only [h', hρ']
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [oracleBudgetInterval, Rat.cast_sum, rationalAllocationCost_cast]
    exact Finset.sum_le_sum (fun i _ => allocationCost_mono (hl i) (hI i).2.2.1 (hx i).2)
  · simp only [oracleBudgetInterval, Rat.cast_sum, rationalAllocationCost_cast]
    exact Finset.sum_le_sum (fun i _ => allocationCost_mono (hx i).1.le (hI i).2.2.2.1 (hu i))
  · simp only [oracleObjectiveInterval, Rat.cast_sum, Rat.cast_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hI i).2.2.1 (by exact_mod_cast (ha i).le))
  · simp only [oracleObjectiveInterval, Rat.cast_sum, Rat.cast_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hI i).2.2.2.1 (by exact_mod_cast (ha i).le))

theorem oracleObjectiveInterval_width {k : ℕ} (a : Fin k → ℚ) (β ρ : ℚ)
    (ha : ∀ i, 0 < a i) (hβ : 0 < β) (n : ℕ)
    (x : Fin k → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hstationary : ∀ i, (a i : ℝ) * (x i) ^ 3 = (β : ℝ) * (1 - (x i) ^ 4) ^ 2)
    (hpole : ∀ i, x i ≤ 1 - (ρ : ℝ)) :
    (oracleObjectiveInterval a β ρ n).2 - (oracleObjectiveInterval a β ρ n).1 ≤
      (∑ i, a i) / 2 ^ n := by
  change (∑ i, a i * _) - (∑ i, a i * _) ≤ _
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have h := (oracleCoordinateInterval_spec (a i) β ρ (ha i) hβ n (hx i).1 (hx i).2
    (hstationary i) (hpole i)).2.2.2.2
  have hmul := mul_le_mul_of_nonneg_left h (ha i).le
  convert hmul using 1 <;> ring

end IdentityTesting.RationalComputation
