import IdentityTesting.Target

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem overlapMoment_summable (q : DiscreteLaw) (δ : ℝ) :
    Summable (fun i => min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)) := by
  apply Summable.of_nonneg_of_le
    (fun i => le_min (q.nonneg i)
      (div_nonneg (Real.rpow_nonneg (q.nonneg i) _) (Real.sqrt_nonneg _)))
    (fun i => min_le_left _ _) q.summable

theorem overlapMoment_nonneg (q : DiscreteLaw) (δ : ℝ) : 0 ≤ overlapMoment q δ := by
  exact tsum_nonneg (fun i => le_min (q.nonneg i)
    (div_nonneg (Real.rpow_nonneg (q.nonneg i) _) (Real.sqrt_nonneg _)))

theorem overlapMoment_le_one (q : DiscreteLaw) (δ : ℝ) : overlapMoment q δ ≤ 1 := by
  have h := (overlapMoment_summable q δ).tsum_le_tsum
    (fun i => min_le_left (q.mass i) _) q.summable
  simpa only [overlapMoment, q.total] using h

theorem overlapMoment_pos (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    0 < overlapMoment q δ := by
  have hpos : ∃ i, 0 < q.mass i := by
    by_contra h
    have hz : q.mass = fun _ => 0 := by
      funext i
      exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (q.nonneg i)
    have ht := q.total
    rw [hz] at ht
    simp at ht
  obtain ⟨i, hi⟩ := hpos
  have hterm : 0 < min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ) :=
    lt_min hi (div_pos (Real.rpow_pos_of_pos hi _) (Real.sqrt_pos.mpr hδ))
  exact hterm.trans_le ((overlapMoment_summable q δ).le_tsum i (fun j _ =>
    le_min (q.nonneg j)
      (div_nonneg (Real.rpow_nonneg (q.nonneg j) _) (Real.sqrt_nonneg _))))

theorem overlapMoment_antitone (q : DiscreteLaw) {δ η : ℝ}
    (hδ : 0 < δ) (hδη : δ ≤ η) : overlapMoment q η ≤ overlapMoment q δ := by
  apply (overlapMoment_summable q η).tsum_le_tsum _ (overlapMoment_summable q δ)
  intro i
  apply min_le_min le_rfl
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (q.nonneg i) _)
    (Real.sqrt_pos.mpr hδ) (Real.sqrt_le_sqrt hδη)

theorem overlapMoment_reciprocal_ge_one (q : DiscreteLaw) {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ 1 / overlapMoment q δ := by
  apply (le_div_iff₀ (overlapMoment_pos q hδ)).mpr
  simpa only [one_mul] using overlapMoment_le_one q δ

end IdentityTesting
