import IdentityTesting.AllocationFiniteTimeBound
import Mathlib.Analysis.MeanInequalities

/-! The sharper finite-support Hölder envelope for the original allocation
supremum. This allows zero weights and does not assume an optimizer. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocation_term_mul_sqrt_le {a t u : ℝ} (ha : 0 ≤ a)
    (ht : 0 < t) (hu : 0 ≤ u) :
    (a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)) * Real.sqrt t ≤
      Real.sqrt a * u ^ (1 / 4 : ℝ) := by
  by_cases haz : a = 0
  · simp [haz]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hd : 0 < u + t ^ 2 * a ^ 2 := by positivity
  have hr : 0 ≤ u / (u + t ^ 2 * a ^ 2) := div_nonneg hu hd.le
  let x := (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)
  let y := u ^ (1 / 4 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg hr _
  have hy : 0 ≤ y := Real.rpow_nonneg hu _
  have hx4 : x ^ 4 = u / (u + t ^ 2 * a ^ 2) := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    norm_num
  have hy4 : y ^ 4 = u := by
    dsimp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
    norm_num
  have heq : x ^ 4 * (u + t ^ 2 * a ^ 2) = u := by
    rw [hx4]
    exact div_mul_cancel₀ _ hd.ne'
  have hm : x ^ 4 * t ^ 2 * a ^ 2 ≤ u := by
    nlinarith only [heq, mul_nonneg hu (pow_nonneg hx 4)]
  have hst4 : Real.sqrt t ^ 4 = t ^ 2 := by
    calc
      _ = (Real.sqrt t ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [Real.sq_sqrt ht.le]
  have hsa4 : Real.sqrt a ^ 4 = a ^ 2 := by
    calc
      _ = (Real.sqrt a ^ 2) ^ 2 := by ring
      _ = a ^ 2 := by rw [Real.sq_sqrt ha]
  change a * x * Real.sqrt t ≤ Real.sqrt a * y
  apply (pow_le_pow_iff_left₀ (by positivity : 0 ≤ a * x * Real.sqrt t)
    (by positivity : 0 ≤ Real.sqrt a * y) (by norm_num : (4 : ℕ) ≠ 0)).mp
  calc
    (a * x * Real.sqrt t) ^ 4 = a ^ 2 * (x ^ 4 * t ^ 2 * a ^ 2) := by
      rw [mul_pow, mul_pow, hst4]
      ring
    _ ≤ a ^ 2 * u := mul_le_mul_of_nonneg_left hm (sq_nonneg a)
    _ = (Real.sqrt a * y) ^ 4 := by rw [mul_pow, hsa4, hy4]

theorem finite_allocation_sum_holder_bound {k : ℕ} (a u : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t)
    (hu : ∀ i, 0 ≤ u i) (hus : (∑ i, u i) ≤ 1) :
    (∑ i, a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) * Real.sqrt t ≤
      (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  have hpq : Real.HolderConjugate (4 / 3 : ℝ) 4 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => Real.sqrt (a i)) (g := fun i => u i ^ (1 / 4 : ℝ)) hpq
    (fun i _ => Real.sqrt_nonneg _) (fun i _ => Real.rpow_nonneg (hu i) _)
  have hf : ∀ i, Real.sqrt (a i) ^ (4 / 3 : ℝ) = a i ^ (2 / 3 : ℝ) := by
    intro i
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (ha i)]
    norm_num
  have hg : ∀ i, (u i ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = u i := by
    intro i
    rw [← Real.rpow_mul (hu i)]
    norm_num
  simp_rw [hf, hg] at hh
  norm_num at hh
  have hu1 : (∑ i, u i) ^ (1 / 4 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => hu i)) hus
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hA : 0 ≤ (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (ha i) _)) _
  calc
    _ = ∑ i, (a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) *
        Real.sqrt t := Finset.sum_mul _ _ _
    _ ≤ ∑ i, Real.sqrt (a i) * u i ^ (1 / 4 : ℝ) :=
      Finset.sum_le_sum (fun i _ => allocation_term_mul_sqrt_le (ha i) ht (hu i))
    _ ≤ (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) * (∑ i, u i) ^ (1 / 4 : ℝ) := hh
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hu1 hA

theorem allocationD_finite_holder_bound {k : ℕ} (a : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t) :
    allocationD (extendFiniteVector a) t ≤
      (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) / Real.sqrt t := by
  apply csSup_le (allocation_values_nonempty _ _)
  rintro v ⟨u, hu, rfl⟩
  rw [countableAllocationObjective_extendFiniteVector_eq_sum]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ht)).2
  exact finite_allocation_sum_holder_bound a (fun i => u i.val) ha ht
    (fun i => hu.1 _) (allocationSimplex_restrict_countable hu).2

theorem allocationD_finite_tail_holder_bound {k : ℕ} (a : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t) :
    allocationD (extendFiniteTailVector a) t ≤
      (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) / Real.sqrt t := by
  apply csSup_le (allocation_values_nonempty _ _)
  rintro v ⟨u, hu, rfl⟩
  rw [countableAllocationObjective_extendFiniteTailVector]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr ht)).2
  exact finite_allocation_sum_holder_bound a (fun i => u i.succ.val) ha ht
    (fun i => hu.1 _) (allocationSimplex_restrict_tail hu).2

theorem finite_allocationRoot_le_holder_bound {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    allocationRoot (extendFiniteLaw q) e ≤
      (∑ i, q.mass i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) / e ^ 2 := by
  obtain ⟨hT, hroot⟩ := allocationRoot_spec (extendFiniteLaw q) he he1
  have hb := allocationD_finite_holder_bound q.mass q.nonneg hT
  rw [extendFiniteVector_probability_mass, hroot] at hb
  have hm := (le_div_iff₀ (Real.sqrt_pos.mpr hT)).mp hb
  have hs := pow_le_pow_left₀ (mul_nonneg he.le (Real.sqrt_nonneg _)) hm 2
  rw [mul_pow, Real.sq_sqrt hT.le] at hs
  have hA : 0 ≤ ∑ i, q.mass i ^ (2 / 3 : ℝ) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)
  have hpow : ((∑ i, q.mass i ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ)) ^ 2 =
      (∑ i, q.mass i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  rw [hpow] at hs
  apply (le_div_iff₀ (sq_pos_of_pos he)).2
  nlinarith only [hs]

theorem finite_heavyRoot_le_tail_holder_bound {k : ℕ}
    (q : FiniteTesting.Probability (Fin (k + 1)))
    (hR0 : 0 < HeavySignedFamily.tailTotal q)
    (hR : HeavySignedFamily.tailTotal q ≤ (1 : ℝ) / 4) {e : ℝ} (he : 0 < e) :
    heavyRoot (extendFiniteLaw q) e ≤
      ((∑ i : Fin k, q.mass i.succ ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) +
        Real.sqrt (HeavySignedFamily.tailTotal q)) ^ 2 / e ^ 2 := by
  have htotal := HeavySignedFamily.reference_head_tail q
  have hq : largestMass (extendFiniteLaw q) < 1 := by
    rw [largestMass_extendFiniteLaw_heavy q hR]
    linarith
  have hT := heavyRoot_pos (extendFiniteLaw q) hq he
  have hroot := heavyRoot_equation (extendFiniteLaw q) hq he
  rw [tailMasses_extendFiniteLaw_heavy q hR, largestMass_extendFiniteLaw_heavy q hR,
    show 1 - q.mass 0 = HeavySignedFamily.tailTotal q by linarith,
    Real.sqrt_div hR0.le] at hroot
  have hb := allocationD_finite_tail_holder_bound (fun i : Fin k => q.mass i.succ)
    (fun i => q.nonneg i.succ) hT
  have hm := (le_div_iff₀ (Real.sqrt_pos.mpr hT)).mp hb
  have hroot' := congrArg (fun x => x * Real.sqrt (heavyRoot (extendFiniteLaw q) e)) hroot
  dsimp only at hroot'
  rw [add_mul, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hT).ne'] at hroot'
  have hbound : e * Real.sqrt (heavyRoot (extendFiniteLaw q) e) ≤
      (∑ i : Fin k, q.mass i.succ ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) +
        Real.sqrt (HeavySignedFamily.tailTotal q) := by
    linarith only [hm, hroot']
  have hs := pow_le_pow_left₀ (mul_nonneg he.le (Real.sqrt_nonneg _)) hbound 2
  rw [mul_pow, Real.sq_sqrt hT.le] at hs
  apply (le_div_iff₀ (sq_pos_of_pos he)).2
  nlinarith only [hs]

end IdentityTesting
