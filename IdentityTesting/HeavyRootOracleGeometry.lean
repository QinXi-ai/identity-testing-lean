import IdentityTesting.RationalAllocationOracle
import IdentityTesting.RationalSqrtInterval
import IdentityTesting.RationalRootSearch
import IdentityTesting.HeavyRoots

open scoped BigOperators
open Set
namespace IdentityTesting.RationalComputation
noncomputable section

def finiteHeavyFunction {k : ℕ} (a : Fin k → ℝ) (t : ℝ) : ℝ :=
  allocationD (extendFiniteVector a) t + Real.sqrt ((∑ i, a i) / t)

def finiteHeavyRoot {k : ℕ} (a : Fin k → ℝ) (e : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ finiteHeavyFunction a t ≤ e}

theorem finiteHeavyFunction_strictAnti {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i) :
    StrictAntiOn (finiteHeavyFunction a) (Ioi 0) := by
  intro t ht u hu htu
  have hd := allocationD_antitone (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable ht.le htu.le
  have hg := Real.sqrt_lt_sqrt (div_nonneg hr.le hu.le)
    (div_lt_div_of_pos_left hr ht htu)
  exact add_lt_add_of_le_of_lt hd hg

theorem finiteHeavyFunction_continuous {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) : ContinuousOn (finiteHeavyFunction a) (Ioi 0) := by
  apply (continuousOn_allocationD (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable).add
  exact (continuousOn_const.div continuousOn_id (fun _ ht => ne_of_gt ht)).sqrt

theorem finiteHeavyRoot_spec_of_bracket {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i) (e L U : ℝ)
    (hL : 0 < L) (hLU : L ≤ U) (hl : e ≤ finiteHeavyFunction a L)
    (hu : finiteHeavyFunction a U ≤ e) :
    0 < finiteHeavyRoot a e ∧ finiteHeavyFunction a (finiteHeavyRoot a e) = e ∧
      L ≤ finiteHeavyRoot a e ∧ finiteHeavyRoot a e ≤ U := by
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hLU
    ((finiteHeavyFunction_continuous a ha).mono (fun x hx => hL.trans_le hx.1)) ⟨hu, hl⟩
  have ht0 : 0 < t := hL.trans_le ht.1
  have hroot : finiteHeavyRoot a e = t :=
    positive_sublevel_sInf_eq (finiteHeavyFunction_strictAnti a ha hr) ht0 heq
  rw [hroot]
  exact ⟨ht0, heq, ht.1, ht.2⟩

theorem finiteHeavyFunction_lower {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i) {e : ℝ} (he : 0 < e) :
    e ≤ finiteHeavyFunction a ((∑ i, a i) / e ^ 2) := by
  have hid : (∑ i, a i) / ((∑ i, a i) / e ^ 2) = e ^ 2 := by field_simp [ne_of_gt hr]
  have hd := (allocationD_bounds ((∑ i, a i) / e ^ 2)
    (extendFiniteVector_nonneg ha) (extendFiniteVector_hasSum a).summable).1
  unfold finiteHeavyFunction
  rw [hid, Real.sqrt_sq_eq_abs, abs_of_pos he]
  linarith

theorem sqrt_scaled_gaps {r m : ℝ} (hr : 0 < r) (hm : 0 < m) :
    Real.sqrt (r / m) / 10 ≤ Real.sqrt (r / (3 * m / 4)) - Real.sqrt (r / m) ∧
      Real.sqrt (r / m) / 10 ≤ Real.sqrt (r / m) - Real.sqrt (r / (3 * m / 2)) := by
  have hbase := Real.sq_sqrt (div_pos hr hm).le
  have hl := Real.sq_sqrt (show 0 ≤ r / (3 * m / 4) by positivity)
  have hu := Real.sq_sqrt (show 0 ≤ r / (3 * m / 2) by positivity)
  have hrl : r / (3 * m / 4) = (4 / 3 : ℝ) * (r / m) := by ring
  have hru : r / (3 * m / 2) = (2 / 3 : ℝ) * (r / m) := by ring
  have hl' := hl.trans hrl
  have hu' := hu.trans hru
  have hleft : (11 / 10 : ℝ) * Real.sqrt (r / m) ≤ Real.sqrt (r / (3 * m / 4)) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    nlinarith only [hl', hbase, sq_nonneg (Real.sqrt (r / m))]
  have hright : Real.sqrt (r / (3 * m / 2)) ≤ (9 / 10 : ℝ) * Real.sqrt (r / m) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith only [hu', hbase, sq_nonneg (Real.sqrt (r / m))]
  constructor <;> linarith

theorem finiteHeavyFunction_scaled_gaps {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i) {m : ℝ} (hm : 0 < m) :
    Real.sqrt ((∑ i, a i) / m) / 10 ≤ finiteHeavyFunction a (3 * m / 4) - finiteHeavyFunction a m ∧
      Real.sqrt ((∑ i, a i) / m) / 10 ≤ finiteHeavyFunction a m - finiteHeavyFunction a (3 * m / 2) := by
  have hdL := allocationD_antitone (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable (by positivity : 0 ≤ 3 * m / 4) (by linarith : 3 * m / 4 ≤ m)
  have hdU := allocationD_antitone (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable hm.le (by linarith : m ≤ 3 * m / 2)
  obtain ⟨hl, hu⟩ := sqrt_scaled_gaps hr hm
  unfold finiteHeavyFunction
  constructor <;> linarith

theorem finiteHeavyFunction_ambiguity_window {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i)
    {m U σ e root : ℝ} (hm : 0 < m) (hmU : m ≤ U) (hσ : 0 < σ)
    (hprecision : 1000 * σ ≤ min 1 ((∑ i, a i) / U))
    (hroot : 0 < root) (hrootEq : finiteHeavyFunction a root = e)
    (hnearL : finiteHeavyFunction a m ≤ e + 2 * σ)
    (hnearU : e ≤ finiteHeavyFunction a m + 2 * σ) :
    3 * m / 4 ≤ root ∧ root ≤ 3 * m / 2 := by
  let z := min 1 ((∑ i, a i) / U)
  have hz0 : 0 ≤ z := le_min (by norm_num) (div_pos hr (hm.trans_le hmU)).le
  have hz1 : z ≤ 1 := min_le_left _ _
  have hzr : z ≤ (∑ i, a i) / m :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_left hr.le hm hmU)
  have hsq : z ^ 2 ≤ (∑ i, a i) / m := by
    have h := mul_le_mul_of_nonneg_left hz1 hz0
    nlinarith only [h, hzr]
  have hzg : z ≤ Real.sqrt ((∑ i, a i) / m) := Real.le_sqrt_of_sq_le hsq
  obtain ⟨hl, hu⟩ := finiteHeavyFunction_scaled_gaps a ha hr hm
  have hleft : e < finiteHeavyFunction a (3 * m / 4) := by
    change 1000 * σ ≤ z at hprecision
    linarith
  have hright : finiteHeavyFunction a (3 * m / 2) < e := by
    change 1000 * σ ≤ z at hprecision
    linarith
  have hf := finiteHeavyFunction_strictAnti a ha hr
  constructor
  · by_contra h
    have hh := hf hroot (by positivity : 0 < 3 * m / 4) (lt_of_not_ge h)
    rw [hrootEq] at hh
    linarith
  · by_contra h
    have hh := hf (by positivity : 0 < 3 * m / 2) hroot (lt_of_not_ge h)
    rw [hrootEq] at hh
    linarith

end
end IdentityTesting.RationalComputation
