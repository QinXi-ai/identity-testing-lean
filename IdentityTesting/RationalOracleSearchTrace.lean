import IdentityTesting.RationalOracleParameterEncoding

/-! The actual parameter-search evaluation trace. Its projection is the
existing oracleSearch result; the list records budget/objective arguments,
including the two objective calls at termination. -/

open scoped BigOperators

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength

def oracleSearchWithTrace (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ) :
    ℕ → ℚ → ℚ → (ℚ × ℚ) × List ℚ
  | 0, l, u => (((objective l).1, (objective u).2), [l, u])
  | n + 1, l, u =>
    if u - l ≤ ζ * l then (((objective l).1, (objective u).2), [l, u])
    else
      let m := (l + u) / 2
      let Q := budget m
      if Q.2 < 1 then
        let r := oracleSearchWithTrace budget objective ζ margin n m u
        (r.1, m :: r.2)
      else if 1 < Q.1 then
        let r := oracleSearchWithTrace budget objective ζ margin n l m
        (r.1, m :: r.2)
      else (((objective m).1 - margin, (objective m).2 + margin), [m, m, m])

theorem oracleSearchWithTrace_result (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ)
    (fuel : ℕ) (l u : ℚ) :
    (oracleSearchWithTrace budget objective ζ margin fuel l u).1 =
      oracleSearch budget objective ζ margin fuel l u := by
  induction fuel generalizing l u with
  | zero => rfl
  | succ fuel ih =>
    simp only [oracleSearchWithTrace, oracleSearch]
    split
    · rfl
    · split
      · exact ih _ _
      · split
        · exact ih _ _
        · rfl

theorem oracleSearchWithTrace_length (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ)
    (fuel : ℕ) (l u : ℚ) :
    (oracleSearchWithTrace budget objective ζ margin fuel l u).2.length ≤ fuel + 2 := by
  induction fuel generalizing l u with
  | zero => simp [oracleSearchWithTrace]
  | succ fuel ih =>
    simp only [oracleSearchWithTrace]
    split
    · simp
    · split
      · simpa only [List.length_cons] using Nat.add_le_add_right (ih ((l + u) / 2) u) 1
      · split
        · simpa only [List.length_cons] using Nat.add_le_add_right (ih l ((l + u) / 2)) 1
        · simp

def dyadicAffine (b B : ℚ) (s j : ℕ) : ℚ := b + (B - b) * ((j : ℚ) / 2 ^ s)

theorem dyadicAffine_encoding_le (b B : ℚ) (s j : ℕ) (hj : j ≤ 2 ^ s) :
    L (dyadicAffine b B s j) ≤ 6 * L b + 4 * L B + 4 * s + 9 := by
  have hx := dyadic_encoding_le s j hj
  have hd := rational_sub_encoding B b
  have hm := rational_mul_encoding (B - b) ((j : ℚ) / 2 ^ s)
  have ha := rational_add_encoding b ((B - b) * ((j : ℚ) / 2 ^ s))
  unfold dyadicAffine
  omega

theorem dyadicAffine_step (b B : ℚ) (s j : ℕ) :
    dyadicAffine b B s j = dyadicAffine b B (s + 1) (2 * j) ∧
    dyadicAffine b B s (j + 1) = dyadicAffine b B (s + 1) (2 * j + 1 + 1) ∧
    (dyadicAffine b B s j + dyadicAffine b B s (j + 1)) / 2 =
      dyadicAffine b B (s + 1) (2 * j + 1) := by
  dsimp only [dyadicAffine]
  push_cast
  rw [pow_succ]
  constructor
  · ring
  · constructor <;> ring

theorem oracleSearchWithTrace_grid_encoding (budget objective : ℚ → ℚ × ℚ)
    (ζ margin b B : ℚ) (fuel s j : ℕ) (hj : j < 2 ^ s) :
    ∀ x ∈ (oracleSearchWithTrace budget objective ζ margin fuel
      (dyadicAffine b B s j) (dyadicAffine b B s (j + 1))).2,
      L x ≤ 6 * L b + 4 * L B + 4 * (s + fuel) + 9 := by
  induction fuel generalizing s j with
  | zero =>
    intro x hx
    simp only [oracleSearchWithTrace, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa using dyadicAffine_encoding_le b B s j hj.le
    · simpa using dyadicAffine_encoding_le b B s (j + 1) (by omega)
  | succ fuel ih =>
    obtain ⟨hl, hu, hm⟩ := dyadicAffine_step b B s j
    have hjl : 2 * j < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hjr : 2 * j + 1 < 2 ^ (s + 1) := by rw [pow_succ]; omega
    have hmid := dyadicAffine_encoding_le b B (s + 1) (2 * j + 1) hjr.le
    simp only [oracleSearchWithTrace]
    split
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have h := dyadicAffine_encoding_le b B s j hj.le
        omega
      · have h := dyadicAffine_encoding_le b B s (j + 1) (by omega)
        omega
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
          simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
          subst x
          omega

theorem oracleSearchWithTrace_encoding_le (budget objective : ℚ → ℚ × ℚ)
    (ζ margin : ℚ) (fuel : ℕ) (b B : ℚ) :
    ∀ x ∈ (oracleSearchWithTrace budget objective ζ margin fuel b B).2,
      L x ≤ 6 * L b + 4 * L B + 4 * fuel + 9 := by
  simpa [dyadicAffine] using
    oracleSearchWithTrace_grid_encoding budget objective ζ margin b B fuel 0 0 (by norm_num)

def allocationOracleWithTrace {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (ℚ × ℚ) × List ℚ :=
  let ρ := oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
  let n := allocationInnerPrecision a t σ
  oracleSearchWithTrace (fun β => oracleBudgetInterval a t β ρ n)
    (fun β => oracleObjectiveInterval a β ρ n) (σ / (100 * ∑ i, a i)) (σ / 100)
    (allocationOuterFuel a t σ) (oracleBetaLower a t) (oracleBetaUpper (a 0) t)

theorem allocationOracleWithTrace_result {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (allocationOracleWithTrace a t σ).1 = allocationOracle a t σ := by
  unfold allocationOracleWithTrace
  rw [oracleSearchWithTrace_result]
  rfl

theorem allocationOracleWithTrace_length {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    (allocationOracleWithTrace a t σ).2.length ≤ 30 * allocationOracleInputLength a t σ + 128 := by
  unfold allocationOracleWithTrace
  apply (oracleSearchWithTrace_length _ _ _ _ _ _ _).trans
  have h := allocationOuterFuel_le a t σ
  omega

theorem allocationOracleWithTrace_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    ∀ x ∈ (allocationOracleWithTrace a t σ).2,
      L x ≤ 180 * allocationOracleInputLength a t σ + 737 := by
  intro x hx
  have h := oracleSearchWithTrace_encoding_le _ _ _ _ _ _ _ x hx
  have hb := oracleBetaLower_encoding_le a t
  have hB := oracleBetaUpper_encoding_le (a 0) t
  have ha := rational_entry_encoding_le a 0
  have hf := allocationOuterFuel_le a t σ
  unfold allocationOracleInputLength at *
  omega

end IdentityTesting.RationalComputation
