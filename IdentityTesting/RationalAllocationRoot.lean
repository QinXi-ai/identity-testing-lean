import IdentityTesting.RationalRootOracleConnection
import IdentityTesting.RationalAllocationOracle
import IdentityTesting.RationalMomentInterval
import IdentityTesting.AllocationRootQuantitative
import IdentityTesting.AllocationTimeSeparation
import IdentityTesting.AllocationFiniteTimeBound

open scoped BigOperators
namespace IdentityTesting.RationalComputation

def allocationRootTolerance {k : ℕ} (q : Fin (k + 1) → ℚ) (e U : ℚ) : ℚ :=
  ((1 - e) ^ 2 * oracleAtomLower q ^ 2 / (100 * (1 + 4 * U ^ 2))) * e

def allocationRootIntervalOn {k : ℕ} (q : Fin (k + 1) → ℚ) (e U : ℚ) : ℚ × ℚ :=
  rootBracket (fun t => allocationOracle q t (allocationRootTolerance q e U)) e (1 - e) U

def rationalAllocationRootInterval {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ) : ℚ × ℚ :=
  allocationRootIntervalOn q e ((k + 1) / e ^ 2)

noncomputable section

theorem allocationRootIntervalOn_spec {k : ℕ} (q : Fin (k + 1) → ℚ) (e U : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (he : 0 < e) (he1 : e < 1)
    (hupper : allocationRoot
      (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e ≤ (U : ℝ)) :
    RootIntervalValid
      (allocationRoot (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e)
      (allocationRootIntervalOn q e U) := by
  let p := extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)
  let b := oracleAtomLower q
  let η := allocationTimeGap ((1 - e : ℚ) : ℝ) (U : ℝ) (b : ℝ) 1
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have he1R : (e : ℝ) < 1 := by exact_mod_cast he1
  have hL : (0 : ℚ) < 1 - e := sub_pos.mpr he1
  have hLR : (0 : ℝ) < ((1 - e : ℚ) : ℝ) := by exact_mod_cast hL
  have hLroot : ((1 - e : ℚ) : ℝ) ≤ allocationRoot p e := by
    simpa only [Rat.cast_sub, Rat.cast_one] using
      (residual_lt_allocationRoot p heR he1R).le
  have hLU : ((1 - e : ℚ) : ℝ) ≤ (U : ℝ) := hLroot.trans hupper
  have hb : (0 : ℝ) < b := by exact_mod_cast oracleAtomLower_pos q hq
  have hqone (i : Fin (k + 1)) : q i ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => (hq j).le) (Finset.mem_univ i)
  have hbr : (b : ℝ) ≤ 1 := by
    exact_mod_cast (oracleAtomLower_le q hq 0).trans (hqone 0)
  have hbds := allocationTimeGap_bounds hLR hb hLU hbr
  have hη : 0 < η := hbds.1
  have hη1 : η < 1 := by dsimp only [η]; linarith only [hbds.2.1]
  have hσeq : (allocationRootTolerance q e U : ℝ) = η * (e : ℝ) := by
    simp only [allocationRootTolerance, η, b, allocationTimeGap]
    push_cast
    ring
  have hσ : 0 < allocationRootTolerance q e U := by
    have hh : (0 : ℝ) < (allocationRootTolerance q e U : ℝ) := by
      rw [hσeq]; exact mul_pos hη heR
    exact_mod_cast hh
  have hrs := allocationRoot_spec p heR he1R
  apply rootBracket_of_oracle_separation (allocationD p.mass) _ e (1 - e) U
    (allocationRootTolerance q e U) (allocationRoot p e) η
    (allocationD_strictAntiOn p.nonneg p.summable p.exists_positive)
    hrs.1 hrs.2 hL hLroot hupper hη.le hη1 he hσeq.le
  · intro m hmL hmU
    exact allocationOracle_spec q m (allocationRootTolerance q e U) hq
      (hL.trans_le hmL) hσ
  · intro m hmL hmU
    have hmLR : ((1 - e : ℚ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmL
    have hmUR : (m : ℝ) ≤ (U : ℝ) := by exact_mod_cast hmU
    have ha : ∀ i, (b : ℝ) ≤ (q i : ℝ) ∧ (q i : ℝ) ≤ 1 := by
      intro i
      constructor
      · exact_mod_cast oracleAtomLower_le q hq i
      · exact_mod_cast hqone i
    have hh := allocationD_finite_time_separation (fun i => (q i : ℝ))
      hLR hb hmLR hmUR hbr ha
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat] using hh.2

theorem rationalAllocationRootInterval_spec {k : ℕ} (q : Fin (k + 1) → ℚ) (e : ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (he : 0 < e) (he1 : e < 1) :
    RootIntervalValid
      (allocationRoot (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) e)
      (rationalAllocationRootInterval q e) := by
  apply allocationRootIntervalOn_spec q e _ hq hs he he1
  have h := finite_allocationRoot_le_card_div_sq (ε := (e : ℝ))
    (rationalFiniteLaw q (fun i => (hq i).le) hs)
    (by exact_mod_cast he) (by exact_mod_cast he1)
  simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_pow,
    Nat.cast_add, Nat.cast_one] using h

end
end IdentityTesting.RationalComputation
