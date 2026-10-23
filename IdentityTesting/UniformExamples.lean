import IdentityTesting.EqualBlockAllocation
import IdentityTesting.FiniteOverlapMoment
import IdentityTesting.CountableCharacterizationRealScale

/-! The concrete uniform reference in the first example of `01_main.tex`.
The reference is a probability on `Fin k`, extended to the original Nat model. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

def uniformFiniteLaw (k : ℕ) (hk : 0 < k) : FiniteTesting.Probability (Fin k) where
  mass := fun _ => 1 / (k : ℝ)
  nonneg := fun _ => by positivity
  total := by simp [Nat.ne_of_gt hk]

def uniformLaw (k : ℕ) (hk : 0 < k) : DiscreteLaw :=
  extendFiniteLaw (uniformFiniteLaw k hk)

/-- Exact optimization formula at the actual uniform probability reference. -/
theorem uniform_allocationD {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    allocationD (uniformLaw k hk).mass t = (1 + t ^ 2 / k) ^ (-1 / 4 : ℝ) := by
  simpa [uniformLaw, uniformFiniteLaw, ← extendFiniteVector_probability_mass] using
    allocationD_equal_block hk ht (by norm_num : (0 : ℝ) < 1)

/-- The actual root has the displayed square; no candidate root equation is
left for the caller. -/
theorem uniform_allocationRoot_sq {k : ℕ} (hk : 0 < k) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    allocationRoot (uniformLaw k hk) e ^ 2 = (k : ℝ) * (1 / e ^ 4 - 1) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  let T := allocationRoot (uniformLaw k hk) e
  have hroot := allocationRoot_spec (uniformLaw k hk) he0 he1
  have hval : (1 + T ^ 2 / k) ^ (-1 / 4 : ℝ) = e := by
    simpa [T, uniform_allocationD hk hroot.1] using hroot.2
  have hb : 0 < 1 + T ^ 2 / k := by positivity
  have hpow : ((1 + T ^ 2 / k) ^ (-1 / 4 : ℝ)) ^ 4 = (1 + T ^ 2 / k)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  have hprod : (1 + T ^ 2 / k) * e ^ 4 = 1 := by
    rw [← hval, hpow]
    exact mul_inv_cancel₀ (ne_of_gt hb)
  change T ^ 2 = (k : ℝ) * (1 / e ^ 4 - 1)
  apply (mul_right_cancel₀ (pow_ne_zero 4 (ne_of_gt he0)))
  have hprod' := congrArg (fun x : ℝ => x * (k : ℝ)) hprod
  field_simp at hprod' ⊢
  nlinarith [hprod']

/-- `A(ε)=sqrt(k)*sqrt(ε⁻⁴-1)`, on the full original radius interval. -/
theorem uniform_allocationRoot {k : ℕ} (hk : 0 < k) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    allocationRoot (uniformLaw k hk) e =
      Real.sqrt (k : ℝ) * Real.sqrt (1 / e ^ 4 - 1) := by
  calc
    allocationRoot (uniformLaw k hk) e =
        Real.sqrt (allocationRoot (uniformLaw k hk) e ^ 2) :=
      (Real.sqrt_sq (allocationRoot_spec (uniformLaw k hk) he0 he1).1.le).symm
    _ = Real.sqrt ((k : ℝ) * (1 / e ^ 4 - 1)) := by rw [uniform_allocationRoot_sq hk he0 he1]
    _ = _ := Real.sqrt_mul (Nat.cast_nonneg k) _

/-- The uniform overlap moment is one whenever the positive overlap parameter
is at most one atom's mass, in particular throughout the manuscript's moment branch. -/
theorem uniform_overlapMoment_eq_one {k : ℕ} (hk : 0 < k) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ 1 / (k : ℝ)) :
    overlapMoment (uniformLaw k hk) δ = 1 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [uniformLaw, overlapMoment_extendFiniteLaw, finiteOverlapMoment]
  have hterm : min (1 / (k : ℝ)) ((1 / (k : ℝ)) ^ (3 / 2 : ℝ) / Real.sqrt δ) =
      1 / (k : ℝ) := by
    apply min_eq_left
    apply (le_div_iff₀ (Real.sqrt_pos.2 hδ)).2
    rw [allocation_three_halves_eq (by positivity : (0 : ℝ) ≤ 1 / k)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsmall) (by positivity)
  simpa only [uniformFiniteLaw, hterm] using (uniformFiniteLaw k hk).total

/-- An explicit version of the near-endpoint algebra in the uniform example. -/
theorem uniform_endpoint_factor_bounds {e : ℝ} (he0 : (1 : ℝ) / 2 ≤ e)
    (he1 : e < 1) :
    1 - e ≤ 1 / e ^ 4 - 1 ∧ 1 / e ^ 4 - 1 ≤ 64 * (1 - e) := by
  have hepos : 0 < e := by linarith
  have he4 : 0 < e ^ 4 := pow_pos hepos 4
  have he4upper : e ^ 4 ≤ 1 := (pow_le_pow_left₀ hepos.le he1.le 4).trans_eq (by norm_num)
  have he4lower : (1 : ℝ) / 16 ≤ e ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) he0 4
    norm_num at h
    exact h
  have he2 : e ^ 2 ≤ 1 := (pow_le_pow_left₀ hepos.le he1.le 2).trans_eq (by norm_num)
  have he3 : e ^ 3 ≤ 1 := (pow_le_pow_left₀ hepos.le he1.le 3).trans_eq (by norm_num)
  have hfactor : 1 / e ^ 4 - 1 = (1 - e) * (1 + e + e ^ 2 + e ^ 3) / e ^ 4 := by
    field_simp
    ring
  rw [hfactor]
  constructor
  · apply (le_div_iff₀ he4).2
    have hpoly : e ^ 4 ≤ 1 + e + e ^ 2 + e ^ 3 := by
      nlinarith [sq_nonneg e, pow_nonneg hepos.le 3]
    exact mul_le_mul_of_nonneg_left hpoly (sub_nonneg.mpr he1.le)
  · apply (div_le_iff₀ he4).2
    have hpoly : 1 + e + e ^ 2 + e ^ 3 ≤ 64 * e ^ 4 := by linarith
    have h := mul_le_mul_of_nonneg_left hpoly (sub_nonneg.mpr he1.le)
    nlinarith

/-- The uniform root is comparable to the collision scale near the endpoint,
with explicit constants and the original root supplied internally. -/
theorem uniform_allocationRoot_near_endpoint {k : ℕ} (hk : 0 < k) {e : ℝ}
    (he0 : (1 : ℝ) / 2 ≤ e) (he1 : e < 1) :
    Real.sqrt ((k : ℝ) * (1 - e)) ≤ allocationRoot (uniformLaw k hk) e ∧
      allocationRoot (uniformLaw k hk) e ≤ 8 * Real.sqrt ((k : ℝ) * (1 - e)) := by
  have hepos : 0 < e := by linarith
  have h := uniform_endpoint_factor_bounds he0 he1
  have hsq := uniform_allocationRoot_sq hk hepos he1
  have hroot := (allocationRoot_spec (uniformLaw k hk) hepos he1).1
  have hsqrt := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr he1.le))
  have hlow := mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg k)
  have hupp := mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg k)
  constructor
  · nlinarith [Real.sqrt_nonneg ((k : ℝ) * (1 - e))]
  · nlinarith [Real.sqrt_nonneg ((k : ℝ) * (1 - e))]

theorem uniform_largestMass {k : ℕ} (hk : 0 < k) :
    largestMass (uniformLaw k hk) = 1 / (k : ℝ) := by
  have hbound : ∀ n, (uniformLaw k hk).mass n ≤ 1 / (k : ℝ) := by
    intro n
    change (if hn : n < k then (1 : ℝ) / k else 0) ≤ 1 / k
    split
    · exact le_rfl
    · positivity
  have hzero : (uniformLaw k hk).mass 0 = 1 / (k : ℝ) := by
    change (if hn : 0 < k then (1 : ℝ) / k else 0) = 1 / k
    simp [hk]
  unfold largestMass
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro x ⟨n, rfl⟩; exact hbound n)
  · rw [← hzero]
    exact le_csSup ⟨1 / (k : ℝ), by rintro x ⟨n, rfl⟩; exact hbound n⟩ ⟨0, rfl⟩

theorem uniform_complexityScale {k : ℕ} (hk : 2 ≤ k) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    complexityScale (uniformLaw k (by omega)) e =
      if (1 / (k : ℝ)) / 2 ≤ 1 - e then allocationRoot (uniformLaw k (by omega)) e else 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkhalf : 1 / (k : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast hk
  rw [complexityScale, uniform_largestMass]
  simp only [ne_of_lt he1, if_false, show ¬(1 / (k : ℝ) = 1) by linarith,
    show ¬(3 / 4 : ℝ) < 1 / k by linarith]
  split_ifs with h
  · rfl
  · rw [uniform_overlapMoment_eq_one (by omega) (sub_pos.mpr he1) (by linarith)]
    norm_num

/-- The manuscript's global uniform scale, including both the allocation and
moment branches, with explicit absolute comparison constants. -/
theorem uniform_complexityScale_bounds {k : ℕ} (hk : 2 ≤ k) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    let q := uniformLaw k (by omega)
    max 1 (allocationRoot q e) ≤ 8 * complexityScale q e ∧
      complexityScale q e ≤ max 1 (allocationRoot q e) := by
  let q := uniformLaw k (by omega)
  change max 1 (allocationRoot q e) ≤ 8 * complexityScale q e ∧
    complexityScale q e ≤ max 1 (allocationRoot q e)
  have hscale := uniform_complexityScale hk he0 he1
  change complexityScale q e =
    (if (1 / (k : ℝ)) / 2 ≤ 1 - e then allocationRoot q e else 1) at hscale
  have hge := complexityScale_ge_one q he0 he1
  by_cases h : (1 / (k : ℝ)) / 2 ≤ 1 - e
  · rw [if_pos h] at hscale
    rw [hscale] at hge ⊢
    rw [max_eq_right hge]
    exact ⟨by linarith, le_rfl⟩
  · rw [if_neg h] at hscale
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkhalf : 1 / (k : ℝ) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast hk
    have hehalf : (1 : ℝ) / 2 ≤ e := by linarith
    have hfactor := (uniform_endpoint_factor_bounds hehalf he1).2
    have hsq := uniform_allocationRoot_sq (show 0 < k by omega) he0 he1
    have hdelta : (k : ℝ) * (1 - e) < 1 / 2 := by
      have h' : 1 - e < (1 / 2 : ℝ) / k := by
        have hquot : (1 / (k : ℝ)) / 2 = (1 / 2 : ℝ) / k := by ring
        rw [hquot] at h
        exact lt_of_not_ge h
      have hd := (lt_div_iff₀ hkpos).mp h'
      simpa [mul_comm] using hd
    have hm := mul_le_mul_of_nonneg_left hfactor hkpos.le
    have hroot8 : allocationRoot q e ≤ 8 := by
      change allocationRoot (uniformLaw k (by omega)) e ≤ 8
      nlinarith [(allocationRoot_spec (uniformLaw k (by omega)) he0 he1).1]
    rw [hscale]
    constructor
    · exact max_le (by norm_num) (by simpa using hroot8)
    · exact le_max_left _ _

/-- Statistical form of the first example, reusing the already proved
countable theorem and the actual uniform scale comparison. -/
theorem uniform_testing_characterization :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (k : ℕ) (hk : 2 ≤ k) (e : ℝ), 0 < e → e < 1 →
        let q := uniformLaw k (by omega)
        let S := max 1 (Real.sqrt (k : ℝ) * Real.sqrt (1 / e ^ 4 - 1))
        (∀ n : ℕ, HasIdentityTest q e n → c * S ≤ n) ∧
        (∃ n : ℕ, HasIdentityTest q e n ∧ (n : ℝ) ≤ C * S) := by
  obtain ⟨c, C, hc, hcC, h⟩ := countable_characterization_realScale
  have hC := hc.trans hcC
  refine ⟨c / 8, C, by positivity, by linarith, ?_⟩
  intro k hk e he0 he1
  let q := uniformLaw k (by omega)
  obtain ⟨hl, hu⟩ := h q e he0 he1.le
  have hb := uniform_complexityScale_bounds hk he0 he1
  dsimp only at hb
  rw [uniform_allocationRoot (show 0 < k by omega) he0 he1] at hb
  constructor
  · intro n hn
    have hm := mul_le_mul_of_nonneg_left hb.1 hc.le
    have hn' := hl n hn
    change c / 8 * _ ≤ (n : ℝ)
    nlinarith
  · obtain ⟨n, hn, hnle⟩ := hu
    exact ⟨n, hn, hnle.trans (mul_le_mul_of_nonneg_left hb.2 hC.le)⟩

/-- The alternative root expression separates the small-radius inverse-square
factor from a factor uniformly bounded away from zero away from ε=1. -/
theorem uniform_allocationRoot_factorization {k : ℕ} (hk : 0 < k) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    allocationRoot (uniformLaw k hk) e =
      (Real.sqrt (k : ℝ) / e ^ 2) * Real.sqrt (1 - e ^ 4) := by
  have he4 : e ^ 4 ≤ 1 := (pow_le_pow_left₀ he0.le he1.le 4).trans_eq (by norm_num)
  rw [uniform_allocationRoot hk he0 he1]
  have hratio : 1 / e ^ 4 - 1 = (1 - e ^ 4) / e ^ 4 := by field_simp
  rw [hratio, Real.sqrt_div (sub_nonneg.mpr he4),
    show e ^ 4 = (e ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg e)]
  ring

/-- For every fixed upper radius b<1, this gives the familiar sqrt(k)/ε²
comparison with an explicit positive lower factor sqrt(1-b⁴). -/
theorem uniform_allocationRoot_away_endpoint {k : ℕ} (hk : 0 < k) {e b : ℝ}
    (he0 : 0 < e) (heb : e ≤ b) (hb1 : b < 1) :
    Real.sqrt (1 - b ^ 4) * (Real.sqrt (k : ℝ) / e ^ 2) ≤
      allocationRoot (uniformLaw k hk) e ∧
      allocationRoot (uniformLaw k hk) e ≤ Real.sqrt (k : ℝ) / e ^ 2 := by
  have he1 := heb.trans_lt hb1
  rw [uniform_allocationRoot_factorization hk he0 he1]
  have hfactor : 0 ≤ Real.sqrt (k : ℝ) / e ^ 2 := by positivity
  constructor
  · have hp := pow_le_pow_left₀ he0.le heb 4
    have hs := Real.sqrt_le_sqrt (show 1 - b ^ 4 ≤ 1 - e ^ 4 by linarith)
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hs hfactor
  · have hs : Real.sqrt (1 - e ^ 4) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
        (show 1 - e ^ 4 ≤ 1 by nlinarith [pow_nonneg he0.le 4])
    exact mul_le_of_le_one_right hfactor hs

/-- The near-endpoint statistical comparison uses max(1,sqrt(k(1-ε)))
and keeps the original strict-alternative testing model. -/
theorem uniform_testing_characterization_near_endpoint :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (k : ℕ) (hk : 2 ≤ k) (e : ℝ), (1 : ℝ) / 2 ≤ e → e < 1 →
        let q := uniformLaw k (by omega)
        let S := max 1 (Real.sqrt ((k : ℝ) * (1 - e)))
        (∀ n : ℕ, HasIdentityTest q e n → c * S ≤ n) ∧
        (∃ n : ℕ, HasIdentityTest q e n ∧ (n : ℝ) ≤ C * S) := by
  obtain ⟨c, C, hc, hcC, h⟩ := uniform_testing_characterization
  have hC := hc.trans hcC
  refine ⟨c, 8 * C, hc, by linarith, ?_⟩
  intro k hk e he0 he1
  have hepos : 0 < e := by linarith
  obtain ⟨hl, hu⟩ := h k hk e hepos he1
  have hb := uniform_allocationRoot_near_endpoint (show 0 < k by omega) he0 he1
  rw [uniform_allocationRoot (show 0 < k by omega) hepos he1] at hb
  have hlo := max_le_max (le_refl (1 : ℝ)) hb.1
  have hup : max 1 (Real.sqrt (k : ℝ) * Real.sqrt (1 / e ^ 4 - 1)) ≤
      8 * max 1 (Real.sqrt ((k : ℝ) * (1 - e))) := by
    apply max_le
    · have hm := le_max_left (1 : ℝ) (Real.sqrt ((k : ℝ) * (1 - e)))
      linarith
    · exact hb.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
  constructor
  · intro n hn
    exact (mul_le_mul_of_nonneg_left hlo hc.le).trans (hl n hn)
  · obtain ⟨n, hn, hnle⟩ := hu
    refine ⟨n, hn, ?_⟩
    have hm := mul_le_mul_of_nonneg_left hup hC.le
    calc
      (n : ℝ) ≤ C * max 1 (Real.sqrt (k : ℝ) * Real.sqrt (1 / e ^ 4 - 1)) := hnle
      _ ≤ C * (8 * max 1 (Real.sqrt ((k : ℝ) * (1 - e)))) := hm
      _ = _ := by ring

end IdentityTesting
