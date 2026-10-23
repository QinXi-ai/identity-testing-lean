import IdentityTesting.RationalOracleParameterEncoding

/-! Polynomial representation-size bounds for the actual allocation-oracle
output, in terms of the original input length. This is independent of a
bit-operation cost model. -/

open scoped BigOperators

namespace IdentityTesting.RationalComputation
local notation "L" => rationalEncodingLength
local notation "V" => rationalVectorEncodingLength

theorem oracleSearch_output_encoding_le (budget objective : ℚ → ℚ × ℚ)
    (ζ margin : ℚ) (K : ℕ)
    (hobj : ∀ x, L (objective x).1 ≤ K ∧ L (objective x).2 ≤ K)
    (fuel : ℕ) (l u : ℚ) :
    L (oracleSearch budget objective ζ margin fuel l u).1 ≤ 2 * (K + L margin) + 1 ∧
      L (oracleSearch budget objective ζ margin fuel l u).2 ≤ 2 * (K + L margin) + 1 := by
  induction fuel generalizing l u with
  | zero =>
    simp only [oracleSearch]
    have hl := (hobj l).1
    have hu := (hobj u).2
    constructor <;> dsimp only <;> omega
  | succ fuel ih =>
    simp only [oracleSearch]
    split
    · have hl := (hobj l).1
      have hu := (hobj u).2
      constructor <;> dsimp only <;> omega
    · split
      · exact ih _ _
      · split
        · exact ih _ _
        · have h := hobj ((l + u) / 2)
          have hl := rational_sub_encoding (objective ((l + u) / 2)).1 margin
          have hu := rational_add_encoding (objective ((l + u) / 2)).2 margin
          constructor <;> dsimp only <;> omega

theorem allocationOracleObjective_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ β : ℚ) :
    let S := allocationOracleInputLength a t σ
    let ρ := oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
    let I := oracleObjectiveInterval a β ρ (allocationInnerPrecision a t σ)
    L I.1 ≤ 184 * S ^ 2 + 888 * S + 3 ∧ L I.2 ≤ 184 * S ^ 2 + 888 * S + 3 := by
  dsimp only
  let S := allocationOracleInputLength a t σ
  have hn := allocationInnerPrecision_le a t σ
  have hρ := allocationOraclePole_encoding_le a t
  have hV : V a ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have hT : L t + V a ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  have hk : k + 1 ≤ S := by
    have h : k + 1 ≤ V a := by unfold rationalVectorEncodingLength; omega
    omega
  have hρ' : L (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)) ≤ 13 * S + 60 := by
    omega
  have hb : 2 * allocationInnerPrecision a t σ +
      2 * L (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)) + 7 ≤ 92 * S + 443 := by
    omega
  have hmul := Nat.mul_le_mul hk hb
  obtain ⟨hl, hu⟩ := oracleObjectiveInterval_encoding_le a β
    (oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)) (allocationInnerPrecision a t σ)
  constructor <;> dsimp only [S] at * <;> nlinarith

theorem allocationOracle_output_encoding_le {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) :
    let S := allocationOracleInputLength a t σ
    L (allocationOracle a t σ).1 ≤ 368 * S ^ 2 + 1778 * S + 25 ∧
      L (allocationOracle a t σ).2 ≤ 368 * S ^ 2 + 1778 * S + 25 := by
  dsimp only
  let ρ := oraclePoleGap (oracleAtomLower a) (oracleBetaUpper (a 0) t)
  let n := allocationInnerPrecision a t σ
  let S := allocationOracleInputLength a t σ
  have hobj : ∀ β, L (oracleObjectiveInterval a β ρ n).1 ≤ 184 * S ^ 2 + 888 * S + 3 ∧
      L (oracleObjectiveInterval a β ρ n).2 ≤ 184 * S ^ 2 + 888 * S + 3 :=
    fun β => allocationOracleObjective_encoding_le a t σ β
  have hm := rational_div_encoding_le σ 100
  have hc := rationalEncodingLength_hundred
  have hσ : L σ ≤ S := by dsimp [S, allocationOracleInputLength]; omega
  obtain ⟨hl, hu⟩ := oracleSearch_output_encoding_le
    (fun β => oracleBudgetInterval a t β ρ n) (fun β => oracleObjectiveInterval a β ρ n)
    (σ / (100 * ∑ i, a i)) (σ / 100) (184 * S ^ 2 + 888 * S + 3) hobj
    (allocationOuterFuel a t σ) (oracleBetaLower a t) (oracleBetaUpper (a 0) t)
  rw [(allocationOracle_eq_boundedPrecision a t σ).1]
  change L (oracleSearch _ _ _ _ _ _ _).1 ≤ _ ∧ L (oracleSearch _ _ _ _ _ _ _).2 ≤ _
  constructor <;> dsimp only [S, n, ρ] at * <;> omega

end IdentityTesting.RationalComputation
