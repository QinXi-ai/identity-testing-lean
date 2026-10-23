import IdentityTesting.CountableAllocationExistence

/-!
# Continuity of the original countable allocation value

On positive time and feasible allocations, the objective is jointly continuous
by the same summable bound as in the fixed-time existence proof.  Maximizing
this actual objective over the compact feasible-allocation subtype gives
continuity of the original supremum `allocationD` on the positive half-line.
-/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem continuous_countableAllocationObjective_subtypes {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    Continuous (fun p : {t : ℝ // 0 < t} × {u : ℕ → ℝ // AllocationFeasible u} =>
      countableAllocationObjective a p.1.1 p.2.1) := by
  unfold countableAllocationObjective
  apply continuous_tsum (u := a) ?_ hasum ?_
  · intro i
    by_cases hz : a i = 0
    · simp only [hz, zero_mul]
      exact continuous_const
    · have ha' : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hz)
      have htime : Continuous (fun p : {t : ℝ // 0 < t} ×
          {u : ℕ → ℝ // AllocationFeasible u} => p.1.1) :=
        continuous_subtype_val.comp continuous_fst
      have hcoord : Continuous (fun p : {t : ℝ // 0 < t} ×
          {u : ℕ → ℝ // AllocationFeasible u} => p.2.1 i) :=
        (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
      apply continuous_const.mul
      apply Continuous.rpow_const _ (fun _ => Or.inr (by norm_num))
      apply hcoord.div (hcoord.add ((htime.pow 2).mul continuous_const))
      intro p
      have ht : 0 < p.1.1 := p.1.2
      have hpos : 0 < p.1.1 ^ 2 * a i ^ 2 := by positivity
      exact ne_of_gt (add_pos_of_nonneg_of_pos (p.2.2.1 i) hpos)
  · intro i p
    rw [Real.norm_eq_abs, abs_of_nonneg (allocation_term_bounds (ha i) (p.2.2.1 i)).1]
    exact (allocation_term_bounds (ha i) (p.2.2.1 i)).2

theorem allocationD_eq_sSup_feasibleSubtype (a : ℕ → ℝ) (t : ℝ) :
    allocationD a t = sSup (Set.range (fun u : {u : ℕ → ℝ // AllocationFeasible u} =>
      countableAllocationObjective a t u.1)) := by
  unfold allocationD
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.1, u.2, rfl⟩

/-- The original supremum is continuous for positive time, with no assumption
of strictly positive weights or positive total mass. -/
theorem continuousOn_allocationD {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    ContinuousOn (allocationD a) (Set.Ioi 0) := by
  letI : CompactSpace {u : ℕ → ℝ // AllocationFeasible u} :=
    isCompact_iff_compactSpace.mp isCompact_allocationFeasible
  have hcont : Continuous (fun t : {t : ℝ // 0 < t} =>
      sSup ((fun u : {u : ℕ → ℝ // AllocationFeasible u} =>
        countableAllocationObjective a t.1 u.1) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set {u : ℕ → ℝ // AllocationFeasible u})).continuous_sSup
      (continuous_countableAllocationObjective_subtypes ha hasum)
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun t : {t : ℝ // 0 < t} => allocationD a t.1)
  simpa only [allocationD_eq_sSup_feasibleSubtype, Set.image_univ] using hcont

end IdentityTesting
