import IdentityTesting.RationalAllocationOracleInputs
import IdentityTesting.RationalAllocationOracleComparison
import IdentityTesting.RationalOracleSearch

/-! The actual rational allocation oracle. Precision and parameter-search fuel
are computed from the inputs; no correctness certificate is supplied by users. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def allocationOracleCoefficient {k : ℕ} (a : Fin (k + 1) → ℚ) (t : ℚ) : ℚ :=
  let B := oracleBetaUpper (a 0) t
  let ρ := oraclePoleGap (oracleAtomLower a) B
  4 * (k + 1) * t ^ 2 * (∑ i, a i) ^ 2 / ρ ^ 2

def allocationOracleWithPrecision {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (n fuel : ℕ) : ℚ × ℚ :=
  let r := ∑ i, a i
  let b := oracleBetaLower a t
  let B := oracleBetaUpper (a 0) t
  let ρ := oraclePoleGap (oracleAtomLower a) B
  let ζ := σ / (100 * r)
  oracleSearch (fun β => oracleBudgetInterval a t β ρ n)
    (fun β => oracleObjectiveInterval a β ρ n) ζ (σ / 100) fuel b B

def allocationOracle {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℚ × ℚ :=
  let r := ∑ i, a i
  let b := oracleBetaLower a t
  let B := oracleBetaUpper (a 0) t
  let M := allocationOracleCoefficient a t
  let ζ := σ / (100 * r)
  let ν := min ζ (ζ / M)
  let n := oracleDyadicPrecision 1 ν
  let fuel := oracleDyadicPrecision (B - b) (ζ * b)
  allocationOracleWithPrecision a t σ n fuel

noncomputable section

theorem allocationOracleWithPrecision_spec {k : ℕ} (a : Fin (k + 1) → ℚ)
    (t σ : ℚ) (ha : ∀ i, 0 < a i) (ht : 0 < t) (hσ : 0 < σ) (n fuel : ℕ)
    (hQwidth : allocationOracleCoefficient a t / 2 ^ n ≤ σ / (100 * ∑ i, a i))
    (hJwidth : (∑ i, a i) / 2 ^ n ≤ σ / 100)
    (hfuel : oracleBetaUpper (a 0) t - oracleBetaLower a t ≤
      2 ^ fuel * (σ / (100 * ∑ i, a i)) * oracleBetaLower a t) :
    OracleIntervalValid (allocationD (extendFiniteVector (fun i => (a i : ℝ))) t) σ
      (allocationOracleWithPrecision a t σ n fuel) := by
  let r := ∑ i, a i
  let b := oracleBetaLower a t
  let B := oracleBetaUpper (a 0) t
  let ρ := oraclePoleGap (oracleAtomLower a) B
  let ζ := σ / (100 * r)
  let Q := fun β => oracleBudgetInterval a t β ρ n
  let J := fun β => oracleObjectiveInterval a β ρ n
  let aR := fun i => (a i : ℝ)
  have hr : 0 < r := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have haR : ∀ i, 0 < aR i := fun i => by
    change (0 : ℝ) < (a i : ℝ)
    exact_mod_cast ha i
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hb : 0 < b := oracleBetaLower_pos a t ha ht
  have hζ : 0 < ζ := div_pos hσ (mul_pos (by norm_num) hr)
  have hζr : (r : ℝ) * (ζ : ℝ) = (σ : ℝ) / 100 := by
    dsimp only [ζ]
    push_cast
    field_simp [ne_of_gt hrR]
  obtain ⟨y, β, hy, hβ, hsy, hbudget, hD, hβlo, hβhi⟩ :=
    exists_actual_oracle_optimizer aR t haR htR 0
  have hbβ : (b : ℝ) ≤ β := by
    simpa only [b, oracleBetaLower, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_sum, aR] using hβlo
  have hβB : β ≤ (B : ℝ) := by
    simpa only [B, oracleBetaUpper, Rat.cast_div, Rat.cast_add, Rat.cast_one,
      Rat.cast_mul, Rat.cast_pow, aR] using hβhi
  have hD' : allocationD (extendFiniteVector aR) t = stationaryObjective aR y := hD
  have hbudget' : stationaryBudget aR y t = 1 := hbudget
  have hlower (γ : ℝ) (h : (b : ℝ) ≤ γ) : 1 ≤ (t : ℝ) ^ 2 * γ * (r : ℝ) := by
    have heq : (b : ℝ) = 1 / ((t : ℝ) ^ 2 * (r : ℝ)) := by
      simp only [b, oracleBetaLower, r, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_sum]
    rw [heq] at h
    have hm := (div_le_iff₀ (mul_pos (sq_pos_of_pos htR) hrR)).mp h
    nlinarith only [hm]
  have heval (m : ℚ) (hbm : b ≤ m) (hmB : m ≤ B) :
      ∃ x : Fin (k + 1) → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
        (∀ i, aR i * x i ^ 3 = (m : ℝ) * (1 - x i ^ 4) ^ 2) ∧
        ((Q m).1 : ℝ) ≤ stationaryBudget aR x t ∧
        stationaryBudget aR x t ≤ ((Q m).2 : ℝ) ∧
        ((J m).1 : ℝ) ≤ stationaryObjective aR x ∧
        stationaryObjective aR x ≤ ((J m).2 : ℝ) ∧
        (Q m).2 - (Q m).1 ≤ ζ ∧ (J m).2 - (J m).1 ≤ σ / 100 := by
    obtain ⟨x, hx, hsx, hbl, hbu, hjl, hju, hqw, hjw⟩ :=
      oracleEvaluation_exists_actual a t m B ha (hb.trans_le hbm) hmB n
    refine ⟨x, hx, hsx, hbl, hbu, hjl, hju, ?_, hjw.trans hJwidth⟩
    apply hqw.trans
    simpa only [allocationOracleCoefficient, Nat.cast_add, Nat.cast_one, B, ζ, r] using hQwidth
  change OracleIntervalValid _ σ (oracleSearch Q J ζ (σ / 100) fuel b B)
  refine oracleSearch_spec Q J ζ (σ / 100) σ b B β _ hζ.le ?_ ?_ ?_ ?_
    fuel b B le_rfl le_rfl hbβ hβB hfuel
  · intro m hbm hmB hlt
    obtain ⟨x, hx, hsx, hbl, hbu, _⟩ := heval m hbm hmB
    by_contra hn
    have hmono := (stationary_sums_mono (t := (t : ℝ)) haR hy hx
      (lt_of_not_ge hn).le hsy hsx).1
    rw [hbudget'] at hmono
    have hltR : ((Q m).2 : ℝ) < 1 := by exact_mod_cast hlt
    linarith only [hmono, hbu, hltR]
  · intro m hbm hmB hlt
    obtain ⟨x, hx, hsx, hbl, hbu, _⟩ := heval m hbm hmB
    by_contra hn
    have hmono := (stationary_sums_mono (t := (t : ℝ)) haR hx hy
      (lt_of_not_ge hn).le hsx hsy).1
    rw [hbudget'] at hmono
    have hltR : (1 : ℝ) < (Q m).1 := by exact_mod_cast hlt
    linarith only [hmono, hbl, hltR]
  · intro l u hbl huB hlβ hβu hwidth
    have hlu : l ≤ u := by exact_mod_cast hlβ.trans hβu
    obtain ⟨x, hx, hsx, _, _, hjl, hju, _, hjw⟩ := heval l hbl (hlu.trans huB)
    obtain ⟨z, hz, hsz, _, _, hzl, hzu, _, hzw⟩ := heval u (hbl.trans hlu) huB
    have hJl := (stationary_sums_mono (t := (t : ℝ)) haR hx hy hlβ hsx hsy).2
    have hJu := (stationary_sums_mono (t := (t : ℝ)) haR hy hz hβu hsy hsz).2
    have hgap := stationary_objective_narrow (ζ := (ζ : ℝ)) haR
      (by exact_mod_cast hb.trans_le hbl) (by exact_mod_cast hlu)
      (by exact_mod_cast hζ.le) (by exact_mod_cast hwidth) hx hz hsx hsz
    have hsum : (∑ i, aR i) = (r : ℝ) := by simp only [r, aR, Rat.cast_sum]
    rw [hsum, hζr] at hgap
    have hjwR : ((J l).2 : ℝ) - ((J l).1 : ℝ) ≤ (σ : ℝ) / 100 := by exact_mod_cast hjw
    have hzwR : ((J u).2 : ℝ) - ((J u).1 : ℝ) ≤ (σ : ℝ) / 100 := by exact_mod_cast hzw
    refine ⟨hjl.trans (by rw [hD']; exact hJl), (by rw [hD']; exact hJu.trans hzu), ?_⟩
    have hw : ((J u).2 : ℝ) - ((J l).1 : ℝ) ≤ (σ : ℝ) := by
      linarith only [hgap, hjwR, hzwR, hzl, hju, hσR]
    exact_mod_cast hw
  · intro m hbm hmB hQl hQu
    obtain ⟨x, hx, hsx, hbl, hbu, hjl, hju, hqw, hjw⟩ := heval m hbm hmB
    have hQlR : ((Q m).1 : ℝ) ≤ 1 := by exact_mod_cast hQl
    have hQuR : (1 : ℝ) ≤ (Q m).2 := by exact_mod_cast hQu
    have hqwR : ((Q m).2 : ℝ) - ((Q m).1 : ℝ) ≤ (ζ : ℝ) := by exact_mod_cast hqw
    have hnear : |stationaryBudget aR x t - 1| ≤ (ζ : ℝ) := by
      rw [abs_le]
      constructor <;> linarith only [hbl, hbu, hQlR, hQuR, hqwR]
    have hnearJ := stationary_ambiguous_budget haR hx hy hrR.le
      (hlower m (by exact_mod_cast hbm)) (hlower β hbβ) hsx hsy hbudget' hnear
    rw [hζr, abs_le] at hnearJ
    have hjwR : ((J m).2 : ℝ) - ((J m).1 : ℝ) ≤ (σ : ℝ) / 100 := by exact_mod_cast hjw
    simp only [OracleIntervalValid, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
    rw [hD']
    refine ⟨?_, ?_, ?_⟩
    · linarith only [hjl, hnearJ.2]
    · linarith only [hju, hnearJ.1]
    · have hw : ((J m).2 : ℝ) + (σ : ℝ) / 100 -
          (((J m).1 : ℝ) - (σ : ℝ) / 100) ≤ (σ : ℝ) := by
        linarith only [hjwR, hσR]
      exact_mod_cast hw

theorem allocationOracle_spec {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ)
    (ha : ∀ i, 0 < a i) (ht : 0 < t) (hσ : 0 < σ) :
    OracleIntervalValid (allocationD (extendFiniteVector (fun i => (a i : ℝ))) t) σ
      (allocationOracle a t σ) := by
  let r := ∑ i, a i
  let b := oracleBetaLower a t
  let B := oracleBetaUpper (a 0) t
  let M := allocationOracleCoefficient a t
  let ζ := σ / (100 * r)
  let ν := min ζ (ζ / M)
  let n := oracleDyadicPrecision 1 ν
  let fuel := oracleDyadicPrecision (B - b) (ζ * b)
  have hr : 0 < r := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hb : 0 < b := oracleBetaLower_pos a t ha ht
  have hB : 0 < B := oracleBetaUpper_pos (ha 0) ht
  have hρ := (oraclePoleGap_spec (oracleAtomLower_pos a ha) hB).1
  have hM : 0 < M := by
    dsimp only [M, allocationOracleCoefficient]
    change 0 < 4 * (k + 1 : ℚ) * t ^ 2 * r ^ 2 /
      (oraclePoleGap (oracleAtomLower a) B) ^ 2
    positivity
  have hζ : 0 < ζ := div_pos hσ (mul_pos (by norm_num) hr)
  have hν : 0 < ν := lt_min hζ (div_pos hζ hM)
  have hn : 1 / 2 ^ n ≤ ν := oracleDyadicPrecision_spec 1 ν hν
  have hζr : r * ζ = σ / 100 := by dsimp only [ζ]; field_simp [ne_of_gt hr]
  have hQ : M / 2 ^ n ≤ ζ := by
    calc
      _ = M * (1 / 2 ^ n) := by ring
      _ ≤ M * ν := mul_le_mul_of_nonneg_left hn hM.le
      _ ≤ M * (ζ / M) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      _ = ζ := by field_simp
  have hJ : r / 2 ^ n ≤ σ / 100 := by
    calc
      _ = r * (1 / 2 ^ n) := by ring
      _ ≤ r * ν := mul_le_mul_of_nonneg_left hn hr.le
      _ ≤ r * ζ := mul_le_mul_of_nonneg_left (min_le_left _ _) hr.le
      _ = _ := hζr
  have hf := oracleDyadicPrecision_spec (B - b) (ζ * b) (mul_pos hζ hb)
  have hfuel : B - b ≤ 2 ^ fuel * ζ * b := by
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ fuel)).mp hf
    nlinarith only [h]
  exact allocationOracleWithPrecision_spec a t σ ha ht hσ n fuel hQ hJ hfuel

end
end IdentityTesting.RationalComputation
