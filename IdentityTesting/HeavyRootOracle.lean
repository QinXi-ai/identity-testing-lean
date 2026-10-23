import IdentityTesting.HeavyRootOracleGeometry
import IdentityTesting.HeavyRootOracleBridge
import IdentityTesting.AllocationFiniteTimeBound
import IdentityTesting.RationalMomentInterval
import IdentityTesting.HeavyFiniteBridge

open scoped BigOperators
namespace IdentityTesting.RationalComputation

def heavyValueOracle {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ) : ℚ × ℚ :=
  let D := allocationOracle a t σ
  let G := sqrtInterval ((∑ i, a i) / t) σ
  (D.1 + G.1, D.2 + G.2)

def heavyOracleLower {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) : ℚ :=
  (∑ i, a i) / e ^ 2

def heavyOracleUpper {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) : ℚ :=
  (k + 2) ^ 2 * (∑ i, a i) / e ^ 2

def heavyOracleTolerance {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) : ℚ :=
  min 1 ((∑ i, a i) / heavyOracleUpper a e) / 1000

def heavyRootOracle {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ) : ℚ × ℚ :=
  rootBracket (fun t => heavyValueOracle a t (heavyOracleTolerance a e)) e
    (heavyOracleLower a e) (heavyOracleUpper a e)

noncomputable section

theorem heavyValueOracle_spec {k : ℕ} (a : Fin (k + 1) → ℚ) (t σ : ℚ)
    (ha : ∀ i, 0 < a i) (ht : 0 < t) (hσ : 0 < σ) :
    OracleIntervalValid (finiteHeavyFunction (fun i => (a i : ℝ)) t) (2 * σ)
      (heavyValueOracle a t σ) := by
  have hr : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  obtain ⟨hdl, hdu, hdw⟩ := allocationOracle_spec a t σ ha ht hσ
  obtain ⟨_, hgl, hgu, hgw⟩ := sqrtInterval_spec ((∑ i, a i) / t) σ (div_pos hr ht).le hσ
  rw [Rat.cast_div, Rat.cast_sum] at hgl hgu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [heavyValueOracle, Rat.cast_add, finiteHeavyFunction] using add_le_add hdl hgl
  · simpa only [heavyValueOracle, Rat.cast_add, finiteHeavyFunction] using add_le_add hdu hgu
  · dsimp only [heavyValueOracle]
    linarith

theorem heavyRootOracle_spec {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ)
    (ha : ∀ i, 0 < a i) (he : 0 < e) :
    RootIntervalValid (finiteHeavyRoot (fun i => (a i : ℝ)) e) (heavyRootOracle a e) := by
  let aR := fun i => (a i : ℝ)
  let r := ∑ i, a i
  let L := heavyOracleLower a e
  let U := heavyOracleUpper a e
  let σ := heavyOracleTolerance a e
  let root := finiteHeavyRoot aR e
  have haR : ∀ i, 0 ≤ aR i := fun i => by
    change (0 : ℝ) ≤ (a i : ℝ)
    exact_mod_cast (ha i).le
  have hr : 0 < r := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hrR : 0 < ∑ i, aR i := by
    dsimp only [aR]
    exact_mod_cast (show 0 < ∑ i, a i from hr)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hL : 0 < L := by dsimp [L, heavyOracleLower]; positivity
  have hU : 0 < U := by dsimp [U, heavyOracleUpper]; positivity
  have hLU : L ≤ U := by
    have hk : (1 : ℚ) ≤ (k + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℚ) k]
    have h := mul_le_mul_of_nonneg_right hk (div_pos hr (sq_pos_of_pos he)).le
    simpa only [one_mul, L, U, heavyOracleLower, heavyOracleUpper, r, mul_div_assoc] using h
  have hl : (e : ℝ) ≤ finiteHeavyFunction aR L := by
    simpa only [L, heavyOracleLower, Rat.cast_div, Rat.cast_sum, Rat.cast_pow, aR] using
      finiteHeavyFunction_lower aR haR hrR heR
  have hu : finiteHeavyFunction aR U ≤ (e : ℝ) := by
    simpa only [U, heavyOracleUpper, finiteHeavyFunction, Rat.cast_div, Rat.cast_mul,
      Rat.cast_sum, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat,
      Nat.cast_add, Nat.cast_one, aR, add_assoc, one_add_one_eq_two] using
      heavy_finite_function_at_upper_bound aR haR hrR heR
  obtain ⟨hroot, hrootEq, hLroot, hrootU⟩ := finiteHeavyRoot_spec_of_bracket aR haR hrR
    e L U (by exact_mod_cast hL) (by exact_mod_cast hLU) hl hu
  have hσ : 0 < σ := by
    dsimp [σ, heavyOracleTolerance]
    exact div_pos (lt_min (by norm_num) (div_pos hr hU)) (by norm_num)
  have hp : 1000 * σ = min 1 (r / U) := by
    dsimp [σ, heavyOracleTolerance, r, U]
    ring
  have hpR : (1000 : ℝ) * (σ : ℝ) ≤ min 1 ((∑ i, aR i) / (U : ℝ)) := by
    have h : (1000 : ℝ) * (σ : ℝ) ≤ min 1 ((r : ℝ) / (U : ℝ)) := by exact_mod_cast hp.le
    simpa only [r, Rat.cast_sum, aR] using h
  have hf := finiteHeavyFunction_strictAnti aR haR hrR
  change RootIntervalValid root (rootBracket (fun t => heavyValueOracle a t σ) e L U)
  apply rootBracket_spec _ e L U root hL hLroot hrootU
  · intro m hLm hmU hleft
    have hm : 0 < m := hL.trans_le hLm
    obtain ⟨hvL, _, _⟩ := heavyValueOracle_spec a m σ ha hm hσ
    have hleftR : (e : ℝ) < (heavyValueOracle a m σ).1 := by exact_mod_cast hleft
    by_contra h
    have hh := hf hroot (by change (0 : ℝ) < (m : ℝ); exact_mod_cast hm) (lt_of_not_ge h)
    rw [hrootEq] at hh
    linarith
  · intro m hLm hmU hright
    have hm : 0 < m := hL.trans_le hLm
    obtain ⟨_, hvU, _⟩ := heavyValueOracle_spec a m σ ha hm hσ
    have hrightR : ((heavyValueOracle a m σ).2 : ℝ) < e := by exact_mod_cast hright
    by_contra h
    have hh := hf (by change (0 : ℝ) < (m : ℝ); exact_mod_cast hm) hroot (lt_of_not_ge h)
    rw [hrootEq] at hh
    linarith
  · intro m hLm hmU hleft hright
    have hm : 0 < m := hL.trans_le hLm
    obtain ⟨hvL, hvU, hwidth⟩ := heavyValueOracle_spec a m σ ha hm hσ
    have hleftR : ((heavyValueOracle a m σ).1 : ℝ) ≤ e := by exact_mod_cast hleft
    have hrightR : (e : ℝ) ≤ (heavyValueOracle a m σ).2 := by exact_mod_cast hright
    have hwR : ((heavyValueOracle a m σ).2 : ℝ) - ((heavyValueOracle a m σ).1 : ℝ) ≤
        2 * (σ : ℝ) := by exact_mod_cast hwidth
    have hnearL : finiteHeavyFunction aR m ≤ (e : ℝ) + 2 * (σ : ℝ) := by linarith
    have hnearU : (e : ℝ) ≤ finiteHeavyFunction aR m + 2 * (σ : ℝ) := by linarith
    have hw := finiteHeavyFunction_ambiguity_window aR haR hrR
      (by exact_mod_cast hm) (by exact_mod_cast hmU) (by exact_mod_cast hσ)
      hpR hroot hrootEq hnearL hnearU
    exact_mod_cast hw

theorem heavyRootOracle_original_spec {k : ℕ} (q : Fin (k + 2) → ℚ) (e : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1)
    (hR : (∑ i : Fin (k + 1), q i.succ) ≤ 1 / 4) (he : 0 < e) :
    let p := rationalFiniteLaw q (fun i => (hq i).le) hs
    RootIntervalValid (heavyRoot (extendFiniteLaw p) e)
      (heavyRootOracle (fun i : Fin (k + 1) => q i.succ) e) := by
  dsimp only
  let p := rationalFiniteLaw q (fun i => (hq i).le) hs
  have hp : ∀ i, 0 < p.mass i := fun i => by
    change (0 : ℝ) < (q i : ℝ)
    exact_mod_cast hq i
  have hR' : HeavySignedFamily.tailTotal p ≤ (1 : ℝ) / 4 := by
    change (∑ i : Fin (k + 1), (q i.succ : ℝ)) ≤ (1 : ℝ) / 4
    have h : ((∑ i : Fin (k + 1), q i.succ : ℚ) : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hR
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  rw [← finiteHeavyRoot_eq_original_heavyRoot p hp hR' (by exact_mod_cast he)]
  exact heavyRootOracle_spec (fun i : Fin (k + 1) => q i.succ) e (fun i => hq i.succ) he

theorem heavyRootOracle_outer_precision_le {k : ℕ} (a : Fin (k + 1) → ℚ) (e : ℚ)
    (ha : ∀ i, 0 < a i) (he : 0 < e) :
    oracleDyadicPrecision (heavyOracleUpper a e - heavyOracleLower a e)
      (heavyOracleLower a e) ≤ 2 * (k + 2).size + 1 := by
  have hr : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  have hL : 0 < heavyOracleLower a e := div_pos hr (sq_pos_of_pos he)
  have hratio : (heavyOracleUpper a e - heavyOracleLower a e) / heavyOracleLower a e =
      ((k + 2 : ℕ) : ℚ) ^ 2 - 1 := by
    have hU : heavyOracleUpper a e = ((k + 2 : ℕ) : ℚ) ^ 2 * heavyOracleLower a e := by
      simp only [heavyOracleUpper, heavyOracleLower, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hU]
    field_simp [ne_of_gt hL]
  have hsize : ((k + 2 : ℕ) : ℚ) ≤ 2 ^ (k + 2).size := by
    exact_mod_cast (Nat.lt_size_self (k + 2)).le
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ ((k + 2 : ℕ) : ℚ)) hsize 2
  have hpow : ((k + 2 : ℕ) : ℚ) ^ 2 - 1 ≤ 2 ^ (2 * (k + 2).size) := by
    rw [Nat.mul_comm 2 (k + 2).size, pow_mul]
    linarith only [hsq]
  apply oracleDyadicPrecision_le
  rwa [hratio]

end
end IdentityTesting.RationalComputation
