import IdentityTesting.AllocationFiniteBridge
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Explicit time separation for the actual finite-support allocation supremum.
The rate is an algebraic expression in positive lower and upper bounds, so a
rational caller can compute it without an optimizer or stationarity witness. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

def allocationTimeGap (L U b r : ℝ) : ℝ :=
  L ^ 2 * b ^ 2 / (100 * (1 + 4 * U ^ 2 * r ^ 2))

theorem allocationTimeGap_bounds {L U b r : ℝ} (hL : 0 < L) (hb : 0 < b)
    (hLU : L ≤ U) (hbr : b ≤ r) :
    0 < allocationTimeGap L U b r ∧ allocationTimeGap L U b r ≤ 1 / 4 ∧
      4 * allocationTimeGap L U b r * (1 + 4 * U ^ 2 * r ^ 2) ≤ L ^ 2 * b ^ 2 / 4 := by
  have hU : 0 < U := hL.trans_le hLU
  have hr : 0 < r := hb.trans_le hbr
  have hprod : L ^ 2 * b ^ 2 ≤ U ^ 2 * r ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ hL.le hLU 2) (pow_le_pow_left₀ hb.le hbr 2)
      (sq_nonneg b) (sq_nonneg U)
  have hB : 0 < 1 + 4 * U ^ 2 * r ^ 2 := by positivity
  have heq : allocationTimeGap L U b r * (1 + 4 * U ^ 2 * r ^ 2) =
      L ^ 2 * b ^ 2 / 100 := by
    unfold allocationTimeGap
    field_simp
  refine ⟨by unfold allocationTimeGap; positivity, ?_, ?_⟩
  · unfold allocationTimeGap
    apply (div_le_iff₀ (by positivity : 0 < 100 * (1 + 4 * U ^ 2 * r ^ 2))).mpr
    nlinarith [mul_nonneg (sq_nonneg U) (sq_nonneg r)]
  · nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg b)]

theorem allocationTimeGap_lt_one {L U b r : ℝ} (hL : 0 < L) (hb : 0 < b)
    (hLU : L ≤ U) (hbr : b ≤ r) : allocationTimeGap L U b r < 1 := by
  have h := (allocationTimeGap_bounds hL hb hLU hbr).2.1
  linarith

theorem allocation_ratio_time_contract {s t a u η : ℝ}
    (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hgap : 4 * η * (1 + t ^ 2 * a ^ 2) ≤ (t ^ 2 - s ^ 2) * a ^ 2) :
    (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤
      (1 - η) * (u / (u + s ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
  have hdS : 0 < u + s ^ 2 * a ^ 2 := by positivity
  have hdT : 0 < u + t ^ 2 * a ^ 2 := by positivity
  have hratio0 : 0 ≤ (u + s ^ 2 * a ^ 2) / (u + t ^ 2 * a ^ 2) := by positivity
  have hratio : (u + s ^ 2 * a ^ 2) / (u + t ^ 2 * a ^ 2) ≤ 1 - 4 * η := by
    apply (div_le_iff₀ hdT).mpr
    have hbud := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ 4 * η)
    nlinarith only [hgap, hbud]
  have hpow : ((u + s ^ 2 * a ^ 2) / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤ 1 - η := by
    apply (Real.rpow_le_rpow hratio0 hratio (by norm_num)).trans
    have h := rpow_one_add_le_one_add_mul_self
      (s := -4 * η) (by linarith) (p := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    convert h using 1 <;> ring
  have heq : u / (u + t ^ 2 * a ^ 2) =
      (u / (u + s ^ 2 * a ^ 2)) * ((u + s ^ 2 * a ^ 2) / (u + t ^ 2 * a ^ 2)) := by
    field_simp
  rw [heq, Real.mul_rpow (div_nonneg hu hdS.le) hratio0]
  calc
    _ ≤ (u / (u + s ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) * (1 - η) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (div_nonneg hu hdS.le) _)
    _ = _ := mul_comm _ _

theorem allocationD_finite_time_contract {k : ℕ} (a : Fin k → ℝ) {s t η : ℝ}
    (ha : ∀ i, 0 < a i) (hs : 0 < s) (ht : 0 < t)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hgap : ∀ i, 4 * η * (1 + t ^ 2 * a i ^ 2) ≤ (t ^ 2 - s ^ 2) * a i ^ 2) :
    allocationD (extendFiniteVector a) t ≤ (1 - η) * allocationD (extendFiniteVector a) s := by
  apply csSup_le (allocation_values_nonempty _ t)
  rintro v ⟨u, hu, rfl⟩
  have hpoint (i : Fin k) :
      a i * (u i.val / (u i.val + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ) ≤
      (1 - η) * (a i * (u i.val / (u i.val + s ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) := by
    have hui : u i.val ≤ 1 :=
      (hu.2.1.le_tsum i.val (fun n _ => hu.1 n)).trans hu.2.2
    have h := mul_le_mul_of_nonneg_left
      (allocation_ratio_time_contract hs ht (ha i) (hu.1 i.val) hui hη0 hη1 (hgap i)) (ha i).le
    convert h using 1 <;> ring
  have hobj : countableAllocationObjective (extendFiniteVector a) t u ≤
      (1 - η) * countableAllocationObjective (extendFiniteVector a) s u := by
    rw [countableAllocationObjective_extendFiniteVector_eq_sum,
      countableAllocationObjective_extendFiniteVector_eq_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  exact hobj.trans (mul_le_mul_of_nonneg_left
    (countableAllocationObjective_le_allocationD s
      (extendFiniteVector_nonneg (fun i => (ha i).le)) (extendFiniteVector_hasSum a).summable hu)
    (by linarith))

theorem allocationTimeGap_atom_gap {L U b r s t a : ℝ}
    (hL : 0 < L) (hb : 0 < b) (hLU : L ≤ U) (hbr : b ≤ r)
    (hba : b ≤ a) (har : a ≤ r) (ht : 0 < t) (htU : t ≤ 2 * U)
    (hsep : L ^ 2 / 4 ≤ t ^ 2 - s ^ 2) :
    4 * allocationTimeGap L U b r * (1 + t ^ 2 * a ^ 2) ≤ (t ^ 2 - s ^ 2) * a ^ 2 := by
  have hU : 0 < U := hL.trans_le hLU
  have ha : 0 < a := hb.trans_le hba
  have ht2 : t ^ 2 ≤ 4 * U ^ 2 := by nlinarith
  have ha2 := pow_le_pow_left₀ ha.le har 2
  have hb2 := pow_le_pow_left₀ hb.le hba 2
  have hcap : t ^ 2 * a ^ 2 ≤ 4 * U ^ 2 * r ^ 2 :=
    mul_le_mul ht2 ha2 (sq_nonneg a) (by positivity)
  have hh := allocationTimeGap_bounds hL hb hLU hbr
  calc
    _ ≤ 4 * allocationTimeGap L U b r * (1 + 4 * U ^ 2 * r ^ 2) := by
      apply mul_le_mul_of_nonneg_left (add_le_add_left hcap 1)
      exact mul_nonneg (by norm_num) hh.1.le
    _ ≤ L ^ 2 * b ^ 2 / 4 := hh.2.2
    _ ≤ (L ^ 2 / 4) * a ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hb2 (sq_nonneg L)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsep (sq_nonneg a)

/-- Uniform contraction on both sides of a trial point. The lower atom bound
may be the minimum atom or any positive rational lower bound such as the
harmonic bound used by the rational allocation oracle. -/
theorem allocationD_finite_time_separation {k : ℕ} (a : Fin k → ℝ) {L U b r m : ℝ}
    (hL : 0 < L) (hb : 0 < b) (hLm : L ≤ m) (hmU : m ≤ U) (hbr : b ≤ r)
    (ha : ∀ i, b ≤ a i ∧ a i ≤ r) :
    0 < allocationTimeGap L U b r ∧
      allocationD (extendFiniteVector a) m ≤
        (1 - allocationTimeGap L U b r) * allocationD (extendFiniteVector a) (3 * m / 4) ∧
      allocationD (extendFiniteVector a) (3 * m / 2) ≤
        (1 - allocationTimeGap L U b r) * allocationD (extendFiniteVector a) m := by
  have hm : 0 < m := hL.trans_le hLm
  have hLU := hLm.trans hmU
  have hU := hm.trans_le hmU
  have hh := allocationTimeGap_bounds hL hb hLU hbr
  have hmass : ∀ i, 0 < a i := fun i => hb.trans_le (ha i).1
  have hLm2 := pow_le_pow_left₀ hL.le hLm 2
  refine ⟨hh.1, ?_, ?_⟩
  · apply allocationD_finite_time_contract a hmass (by positivity) hm hh.1.le hh.2.1
    intro i
    exact allocationTimeGap_atom_gap hL hb hLU hbr (ha i).1 (ha i).2 hm
      (by linarith) (by nlinarith [sq_nonneg m])
  · apply allocationD_finite_time_contract a hmass hm (by positivity) hh.1.le hh.2.1
    intro i
    exact allocationTimeGap_atom_gap hL hb hLU hbr (ha i).1 (ha i).2 (by positivity)
      (by linarith) (by nlinarith [sq_nonneg m])

end IdentityTesting
