import IdentityTesting.RationalRootSearch
import IdentityTesting.RationalOracleSearchTrace

/-! Source-level evaluation arguments and output representation sizes for the
actual rational root search. No cost of evaluating the oracle is assumed here. -/

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def rootSearchWithTrace (evaluate : ℚ → ℚ × ℚ) (e : ℚ) :
    ℕ → ℚ → ℚ → (ℚ × ℚ) × List ℚ
  | 0, l, u => ((l, u), [])
  | n + 1, l, u =>
      if u ≤ 2 * l then ((l, u), [])
      else
        let m := (l + u) / 2
        let I := evaluate m
        if e < I.1 then
          let r := rootSearchWithTrace evaluate e n m u
          (r.1, m :: r.2)
        else if I.2 < e then
          let r := rootSearchWithTrace evaluate e n l m
          (r.1, m :: r.2)
        else ((max l (3 * m / 4), min u (3 * m / 2)), [m])

theorem rootSearchWithTrace_result (evaluate : ℚ → ℚ × ℚ) (e : ℚ)
    (fuel : ℕ) (l u : ℚ) :
    (rootSearchWithTrace evaluate e fuel l u).1 = rootSearch evaluate e fuel l u := by
  induction fuel generalizing l u with
  | zero => rfl
  | succ fuel ih =>
    simp only [rootSearchWithTrace, rootSearch]
    split
    · rfl
    · split
      · exact ih _ _
      · split
        · exact ih _ _
        · rfl

theorem rootSearchWithTrace_length (evaluate : ℚ → ℚ × ℚ) (e : ℚ)
    (fuel : ℕ) (l u : ℚ) :
    (rootSearchWithTrace evaluate e fuel l u).2.length ≤ fuel := by
  induction fuel generalizing l u with
  | zero => simp [rootSearchWithTrace]
  | succ fuel ih =>
    simp only [rootSearchWithTrace]
    split
    · simp
    · split
      · simpa only [List.length_cons] using Nat.add_le_add_right (ih ((l + u) / 2) u) 1
      · split
        · simpa only [List.length_cons] using Nat.add_le_add_right (ih l ((l + u) / 2)) 1
        · simp

theorem rootSearchWithTrace_grid_encoding (evaluate : ℚ → ℚ × ℚ)
    (e b B : ℚ) (fuel s j : ℕ) (hj : j < 2 ^ s) :
    ∀ x ∈ (rootSearchWithTrace evaluate e fuel
      (dyadicAffine b B s j) (dyadicAffine b B s (j + 1))).2,
      L x ≤ 6 * L b + 4 * L B + 4 * (s + fuel) + 9 := by
  induction fuel generalizing s j with
  | zero => simp [rootSearchWithTrace]
  | succ fuel ih =>
    obtain ⟨hl, hu, hm⟩ := dyadicAffine_step b B s j
    have hjl : 2 * j < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hjr : 2 * j + 1 < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hmid := dyadicAffine_encoding_le b B (s + 1) (2 * j + 1) hjr.le
    simp only [rootSearchWithTrace]
    split
    · simp
    · rw [hm]
      split
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · rw [hu] at hx
          have h := ih (s + 1) (2 * j + 1) hjr x hx
          omega
      · split
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · rw [hl] at hx
            have h := ih (s + 1) (2 * j) hjl x hx
            omega
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst x
          omega

theorem rootSearchWithTrace_encoding_le (evaluate : ℚ → ℚ × ℚ)
    (e : ℚ) (fuel : ℕ) (b B : ℚ) :
    ∀ x ∈ (rootSearchWithTrace evaluate e fuel b B).2,
      L x ≤ 6 * L b + 4 * L B + 4 * fuel + 9 := by
  simpa [dyadicAffine] using
    rootSearchWithTrace_grid_encoding evaluate e b B fuel 0 0 (by norm_num)

private theorem rootSearch_output_grid_encoding (evaluate : ℚ → ℚ × ℚ)
    (e b B : ℚ) (fuel s j : ℕ) (hj : j < 2 ^ s) :
    let I := rootSearch evaluate e fuel
      (dyadicAffine b B s j) (dyadicAffine b B s (j + 1))
    let K := 6 * L b + 4 * L B + 4 * (s + fuel) + 9 + L 3 + L 4 + L 2
    L I.1 ≤ K ∧ L I.2 ≤ K := by
  dsimp only
  induction fuel generalizing s j with
  | zero =>
    have hl := dyadicAffine_encoding_le b B s j hj.le
    have hu := dyadicAffine_encoding_le b B s (j + 1) (by omega)
    simp only [rootSearch]
    constructor <;> omega
  | succ fuel ih =>
    obtain ⟨hl, hu, hm⟩ := dyadicAffine_step b B s j
    have hjl : 2 * j < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hjr : 2 * j + 1 < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hleft := dyadicAffine_encoding_le b B s j hj.le
    have hright := dyadicAffine_encoding_le b B s (j + 1) (by omega)
    have hmid := dyadicAffine_encoding_le b B (s + 1) (2 * j + 1) hjr.le
    simp only [rootSearch]
    split
    · constructor <;> dsimp only <;> omega
    · rw [hm]
      split
      · rw [hu]
        obtain ⟨h1, h2⟩ := ih (s + 1) (2 * j + 1) hjr
        constructor <;> omega
      · split
        · rw [hl]
          obtain ⟨h1, h2⟩ := ih (s + 1) (2 * j) hjl
          constructor <;> omega
        · have hmul := rational_mul_encoding 3 (dyadicAffine b B (s + 1) (2 * j + 1))
          have hdiv4 := rational_div_encoding_le (3 * dyadicAffine b B (s + 1) (2 * j + 1)) 4
          have hdiv2 := rational_div_encoding_le (3 * dyadicAffine b B (s + 1) (2 * j + 1)) 2
          dsimp only
          constructor
          · rcases le_total (dyadicAffine b B s j) (3 * dyadicAffine b B (s + 1) (2 * j + 1) / 4) with h | h
            · rw [max_eq_right h]; omega
            · rw [max_eq_left h]; omega
          · rcases le_total (dyadicAffine b B s (j + 1)) (3 * dyadicAffine b B (s + 1) (2 * j + 1) / 2) with h | h
            · rw [min_eq_left h]; omega
            · rw [min_eq_right h]; omega

theorem rootSearch_output_encoding_le (evaluate : ℚ → ℚ × ℚ)
    (e : ℚ) (fuel : ℕ) (b B : ℚ) :
    let I := rootSearch evaluate e fuel b B
    let K := 6 * L b + 4 * L B + 4 * fuel + 9 + L 3 + L 4 + L 2
    L I.1 ≤ K ∧ L I.2 ≤ K := by
  simpa [dyadicAffine] using
    rootSearch_output_grid_encoding evaluate e b B fuel 0 0 (by norm_num)

theorem rootSearch_output_encoding_le_numeric (evaluate : ℚ → ℚ × ℚ)
    (e : ℚ) (fuel : ℕ) (b B : ℚ) :
    L (rootSearch evaluate e fuel b B).1 ≤ 6 * L b + 4 * L B + 4 * fuel + 22 ∧
      L (rootSearch evaluate e fuel b B).2 ≤ 6 * L b + 4 * L B + 4 * fuel + 22 := by
  have h2 : (2 : ℕ).size = 2 := by simpa using (Nat.size_pow (n := 1))
  have h4 : (4 : ℕ).size = 3 := by simpa using (Nat.size_pow (n := 2))
  have h3 : (3 : ℕ).size = 2 := by
    have hl : (3 : ℕ).size ≤ 2 := Nat.size_le.mpr (by norm_num)
    have hu : 1 < (3 : ℕ).size := Nat.lt_size.mpr (by norm_num)
    omega
  have hc2 : L 2 = 4 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h2]
  have hc3 : L 3 = 4 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h3]
  have hc4 : L 4 = 5 := by norm_num [rationalEncodingLength, numeratorBits, denominatorBits, h4]
  simpa only [hc2, hc3, hc4, Nat.add_assoc] using rootSearch_output_encoding_le evaluate e fuel b B

end IdentityTesting.RationalComputation
