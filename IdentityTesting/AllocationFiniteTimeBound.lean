import IdentityTesting.HeavyFiniteBridge

/-! Explicit finite-support time bounds for the original allocation supremum
and its original sublevel-infimum roots. Zero vector entries are allowed. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocation_term_sq_le_div {a t u : ℝ} (ha : 0 ≤ a)
    (ht : 0 < t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)) ^ 2 ≤ a / t := by
  by_cases haz : a = 0
  · simp [haz]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hd : 0 < u + t ^ 2 * a ^ 2 := by positivity
  have hr : 0 ≤ u / (u + t ^ 2 * a ^ 2) := div_nonneg hu0 hd.le
  let x := (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg hr _
  have hx4 : x ^ 4 = u / (u + t ^ 2 * a ^ 2) := by
    dsimp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    norm_num
  have heq : x ^ 4 * (u + t ^ 2 * a ^ 2) = u := by
    rw [hx4]
    exact div_mul_cancel₀ _ hd.ne'
  have hb : t ^ 2 * a ^ 2 * x ^ 4 ≤ 1 := by
    nlinarith only [heq, hu1, mul_nonneg hu0 (pow_nonneg hx 4)]
  have hb' : t * a * x ^ 2 ≤ 1 :=
    (sq_le_sq₀ (by positivity : 0 ≤ t * a * x ^ 2) zero_le_one).mp
      (by nlinarith only [hb])
  have hm := mul_le_mul_of_nonneg_left hb' ha
  apply (le_div_iff₀ ht).2
  change (a * x) ^ 2 * t ≤ a
  nlinarith only [hm]

theorem finite_allocation_sum_sq_time_bound {k : ℕ} (a u : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t)
    (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∀ i, u i ≤ 1) :
    (∑ i, a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)) ^ 2 ≤
      (k : ℝ) * (∑ i, a i) / t := by
  let f := fun i => a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)
  have hc : (∑ i, f i) ^ 2 ≤ (k : ℝ) * ∑ i, f i ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin k => (1 : ℝ)) f)
  have hs : (∑ i, f i ^ 2) ≤ (∑ i, a i) / t := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => allocation_term_sq_le_div (ha i) ht (hu0 i) (hu1 i))
  exact hc.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k))

/-- A concrete cardinality/mass envelope for the actual allocation supremum. -/
theorem allocationD_finite_sq_time_bound {k : ℕ} (a : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t) :
    allocationD (extendFiniteVector a) t ^ 2 ≤ (k : ℝ) * (∑ i, a i) / t := by
  have hc : 0 ≤ (k : ℝ) * (∑ i, a i) / t :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) (Finset.sum_nonneg (fun i _ => ha i))) ht.le
  have hbound : allocationD (extendFiniteVector a) t ≤
      Real.sqrt ((k : ℝ) * (∑ i, a i) / t) := by
    apply csSup_le (allocation_values_nonempty _ _)
    rintro v ⟨u, hu, rfl⟩
    rw [countableAllocationObjective_extendFiniteVector_eq_sum]
    apply Real.le_sqrt_of_sq_le
    exact finite_allocation_sum_sq_time_bound a (fun i => u i.val) ha ht
      (fun i => hu.1 _) (fun i => allocationFeasible_coordinate_le_one_for_limits hu _)
  exact (Real.le_sqrt (allocationD_bounds t (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable).1 hc).mp hbound

/-- A simple finite cardinality envelope for an unnormalized vector. -/
theorem heavy_finite_function_time_bound {k : ℕ} (a : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t) :
    allocationD (extendFiniteVector a) t + Real.sqrt ((∑ i, a i) / t) ≤
      ((k : ℝ) + 1) * Real.sqrt ((∑ i, a i) / t) := by
  let g := Real.sqrt ((∑ i, a i) / t)
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = (∑ i, a i) / t :=
    Real.sq_sqrt (div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) ht.le)
  have hD := allocationD_finite_sq_time_bound a ha ht
  have hkg : allocationD (extendFiniteVector a) t ^ 2 ≤ (k : ℝ) * g ^ 2 := by
    simpa only [hg2, mul_div_assoc] using hD
  have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast (show k ≤ k ^ 2 by simpa [pow_two] using Nat.le_mul_self k)
  have hks := mul_le_mul_of_nonneg_right hk (sq_nonneg g)
  have hD0 := (allocationD_bounds t (extendFiniteVector_nonneg ha)
    (extendFiniteVector_hasSum a).summable).1
  have hDg : allocationD (extendFiniteVector a) t ≤ (k : ℝ) * g :=
    (sq_le_sq₀ hD0 (mul_nonneg (Nat.cast_nonneg k) hg)).mp
      (by nlinarith only [hkg, hks])
  change allocationD (extendFiniteVector a) t + g ≤ ((k : ℝ) + 1) * g
  nlinarith only [hDg]

/-- The explicit finite-vector upper endpoint used by rational heavy-root
search. This is an inequality for the original supremum, not a supplied root
or optimizer certificate. -/
theorem heavy_finite_function_at_upper_bound {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑ i, a i) {e : ℝ} (he : 0 < e) :
    allocationD (extendFiniteVector a) (((k : ℝ) + 1) ^ 2 * (∑ i, a i) / e ^ 2) +
      Real.sqrt ((∑ i, a i) / (((k : ℝ) + 1) ^ 2 * (∑ i, a i) / e ^ 2)) ≤ e := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hU : 0 < ((k : ℝ) + 1) ^ 2 * (∑ i, a i) / e ^ 2 := by positivity
  have hs : Real.sqrt ((∑ i, a i) /
      (((k : ℝ) + 1) ^ 2 * (∑ i, a i) / e ^ 2)) = e / ((k : ℝ) + 1) := by
    apply (Real.sqrt_eq_iff_eq_sq (div_nonneg hr.le hU.le) (div_nonneg he.le hk.le)).2
    field_simp
    <;> ring
  have hb := heavy_finite_function_time_bound a ha hU
  rw [hs] at hb
  have hc : ((k : ℝ) + 1) * (e / ((k : ℝ) + 1)) = e := by
    field_simp
  rw [hs]
  rwa [hc] at hb

theorem allocationD_finite_probability_at_upper_bound {k : ℕ}
    (q : FiniteTesting.Probability (Fin (k + 1))) {e : ℝ} (he : 0 < e) :
    allocationD (extendFiniteLaw q).mass (((k : ℝ) + 1) / e ^ 2) ≤ e := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hU : 0 < ((k : ℝ) + 1) / e ^ 2 := by positivity
  have hb := allocationD_finite_sq_time_bound q.mass q.nonneg hU
  rw [extendFiniteVector_probability_mass, q.total, mul_one] at hb
  have hc : ((k + 1 : ℕ) : ℝ) / (((k : ℝ) + 1) / e ^ 2) = e ^ 2 := by
    push_cast
    field_simp
  rw [hc] at hb
  exact (sq_le_sq₀ (allocationD_bounds _ (extendFiniteLaw q).nonneg
    (extendFiniteLaw q).summable).1 he.le).mp hb

theorem allocationD_finite_tail_sq_time_bound {k : ℕ} (a : Fin k → ℝ) {t : ℝ}
    (ha : ∀ i, 0 ≤ a i) (ht : 0 < t) :
    allocationD (extendFiniteTailVector a) t ^ 2 ≤ (k : ℝ) * (∑ i, a i) / t := by
  have han : ∀ i, 0 ≤ extendFiniteTailVector a i := by
    intro i
    cases i with
    | zero => exact le_rfl
    | succ i => exact extendFiniteVector_nonneg ha i
  have hc : 0 ≤ (k : ℝ) * (∑ i, a i) / t :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) (Finset.sum_nonneg (fun i _ => ha i))) ht.le
  have hbound : allocationD (extendFiniteTailVector a) t ≤
      Real.sqrt ((k : ℝ) * (∑ i, a i) / t) := by
    apply csSup_le (allocation_values_nonempty _ _)
    rintro v ⟨u, hu, rfl⟩
    rw [countableAllocationObjective_extendFiniteTailVector]
    apply Real.le_sqrt_of_sq_le
    exact finite_allocation_sum_sq_time_bound a (fun i => u i.succ.val) ha ht
      (fun i => hu.1 _) (fun i => allocationFeasible_coordinate_le_one_for_limits hu _)
  exact (Real.le_sqrt (allocationD_bounds t han
    (extendFiniteTailVector_hasSum a).summable).1 hc).mp hbound

/-- The full allocation root has a concrete initial upper bound for every
finite probability vector, even when some entries are zero. -/
theorem finite_allocationRoot_le_card_div_sq {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    allocationRoot (extendFiniteLaw q) ε ≤ (k : ℝ) / ε ^ 2 := by
  obtain ⟨hT, hroot⟩ := allocationRoot_spec (extendFiniteLaw q) hε0 hε1
  have hb := allocationD_finite_sq_time_bound q.mass q.nonneg hT
  rw [extendFiniteVector_probability_mass, hroot, q.total, mul_one] at hb
  have hm := (le_div_iff₀ hT).mp hb
  apply (le_div_iff₀ (sq_pos_of_pos hε0)).2
  nlinarith only [hm]

private theorem heavy_equation_time_bound (k : ℕ) {D T R e : ℝ}
    (hD0 : 0 ≤ D) (hT : 0 < T) (hR : 0 ≤ R) (he : 0 < e)
    (hD : D ^ 2 ≤ (k : ℝ) * R / T)
    (hroot : D + Real.sqrt (R / T) = e) :
    T ≤ ((k : ℝ) + 1) ^ 2 * R / e ^ 2 := by
  let g := Real.sqrt (R / T)
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  have hg2 : g ^ 2 = R / T := Real.sq_sqrt (div_nonneg hR hT.le)
  have hkg : D ^ 2 ≤ (k : ℝ) * g ^ 2 := by simpa only [hg2, mul_div_assoc] using hD
  have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast (show k ≤ k ^ 2 by simpa [pow_two] using Nat.le_mul_self k)
  have hks := mul_le_mul_of_nonneg_right hk (sq_nonneg g)
  have hDg : D ≤ (k : ℝ) * g :=
    (sq_le_sq₀ hD0 (mul_nonneg (Nat.cast_nonneg k) hg)).mp (by nlinarith only [hkg, hks])
  have heg : e ≤ ((k : ℝ) + 1) * g := by change D + g = e at hroot; nlinarith only [hroot, hDg]
  have hegsq := pow_le_pow_left₀ he.le heg 2
  have hscaled := mul_le_mul_of_nonneg_right hegsq hT.le
  have hgt : g ^ 2 * T = R := (eq_div_iff hT.ne').mp hg2
  apply (le_div_iff₀ (sq_pos_of_pos he)).2
  nlinarith only [hscaled, congrArg (fun x => ((k : ℝ) + 1) ^ 2 * x) hgt]

/-- A root bound using the number of tail atoms when the designated head is at
zero and has mass at least 3/4. The root and all tail weights are constructed. -/
theorem finite_heavyRoot_le_tail_card_bound {k : ℕ}
    (q : FiniteTesting.Probability (Fin (k + 1)))
    (hR0 : 0 < HeavySignedFamily.tailTotal q)
    (hR : HeavySignedFamily.tailTotal q ≤ (1 : ℝ) / 4)
    {e : ℝ} (he : 0 < e) :
    heavyRoot (extendFiniteLaw q) e ≤
      ((k : ℝ) + 1) ^ 2 * HeavySignedFamily.tailTotal q / e ^ 2 := by
  have htotal := HeavySignedFamily.reference_head_tail q
  have hq : largestMass (extendFiniteLaw q) < 1 := by
    rw [largestMass_extendFiniteLaw_heavy q hR]
    linarith
  have hroot := heavyRoot_equation (extendFiniteLaw q) hq he
  have hT := heavyRoot_pos (extendFiniteLaw q) hq he
  rw [tailMasses_extendFiniteLaw_heavy q hR, largestMass_extendFiniteLaw_heavy q hR,
    show 1 - q.mass 0 = HeavySignedFamily.tailTotal q by linarith] at hroot
  apply heavy_equation_time_bound k
    (allocationD_bounds _ (by
      intro i
      cases i with
      | zero => exact le_rfl
      | succ i => exact extendFiniteVector_nonneg (fun i => q.nonneg i.succ) i)
      (extendFiniteTailVector_hasSum (fun i : Fin k => q.mass i.succ)).summable).1 hT hR0.le he _ hroot
  exact allocationD_finite_tail_sq_time_bound (fun i : Fin k => q.mass i.succ)
    (fun i => q.nonneg i.succ) hT

/-- Arbitrary finite placement of the largest atom: at most k tail entries
suffice, including its zeroed head entry. No positivity or head-location premise. -/
theorem finite_heavyRoot_le_card_bound {k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (hq : largestMass (extendFiniteLaw q) < 1)
    {e : ℝ} (he : 0 < e) :
    heavyRoot (extendFiniteLaw q) e ≤
      ((k : ℝ) + 1) ^ 2 * (1 - largestMass (extendFiniteLaw q)) / e ^ 2 := by
  let a : Fin k → ℝ := fun i => tailMasses (extendFiniteLaw q) i.val
  have ha : ∀ i, 0 ≤ a i := fun i => tailMasses_nonneg _ _
  have hext : extendFiniteVector a = tailMasses (extendFiniteLaw q) := by
    funext n
    by_cases hn : n < k
    · rw [show extendFiniteVector a n = a ⟨n, hn⟩ from extendFiniteVector_val a ⟨n, hn⟩]
    · simp only [extendFiniteVector, dif_neg hn, tailMasses]
      split_ifs
      · rfl
      · exact (extendFiniteLaw_mass_of_not_lt q n hn).symm
  have hsum : (∑ i, a i) = 1 - largestMass (extendFiniteLaw q) := by
    rw [← (extendFiniteVector_hasSum a).tsum_eq, hext]
    exact tailMasses_total _
  have hT := heavyRoot_pos (extendFiniteLaw q) hq he
  apply heavy_equation_time_bound k
    (allocationD_bounds _ (tailMasses_nonneg _) (tailMasses_summable _)).1 hT
    (sub_pos.mpr hq).le he _ (heavyRoot_equation (extendFiniteLaw q) hq he)
  have hb := allocationD_finite_sq_time_bound a ha hT
  rwa [hext, hsum] at hb

end IdentityTesting
