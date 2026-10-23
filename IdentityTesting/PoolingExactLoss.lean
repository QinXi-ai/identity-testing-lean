import IdentityTesting.CountablePooling

/-! Exact TV loss when an arbitrary finite set is retained and its complement pooled. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators

theorem pooledLaw_tv_loss_eq_overlap (p q : DiscreteLaw) (s : Finset ℕ) :
    totalVariation p q - FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) =
      min (residualMass p s) (residualMass q s) - residualOverlap p q s := by
  rw [pooledLaw_totalVariation, totalVariation_eq_one_sub_overlap, ← overlap_split p q s]
  unfold pooledTVFormula
  ring

theorem pooledLaw_tv_loss_eq_abs (p q : DiscreteLaw) (s : Finset ℕ) :
    totalVariation p q - FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) =
      ((∑' i : {i : ℕ // i ∉ s}, |p.mass i - q.mass i|) -
        |residualMass p s - residualMass q s|) / 2 := by
  rw [pooledLaw_tv_loss_eq_overlap]
  have hp : Summable (fun i : {i : ℕ // i ∉ s} => p.mass i) := p.summable.subtype _
  have hq : Summable (fun i : {i : ℕ // i ∉ s} => q.mass i) := q.summable.subtype _
  have hm : Summable (fun i : {i : ℕ // i ∉ s} => min (p.mass i) (q.mass i)) :=
    (p.summable_min q).subtype _
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [(hp.add hq).tsum_sub (hm.mul_left 2), hp.tsum_add hq, tsum_mul_left]
  unfold residualMass residualOverlap
  ring

theorem pooledLaw_tv_loss_bounds (p q : DiscreteLaw) (s : Finset ℕ) :
    0 ≤ totalVariation p q - FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) ∧
    totalVariation p q - FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) ≤
      min (residualMass p s) (residualMass q s) ∧
    min (residualMass p s) (residualMass q s) ≤ residualMass q s := by
  rw [pooledLaw_tv_loss_eq_overlap]
  have hm := (p.summable_min q).subtype (fun i => i ∉ s)
  have hp : residualOverlap p q s ≤ residualMass p s :=
    hm.tsum_le_tsum (fun i => min_le_left _ _) (p.summable.subtype _)
  have hq : residualOverlap p q s ≤ residualMass q s :=
    hm.tsum_le_tsum (fun i => min_le_right _ _) (q.summable.subtype _)
  exact ⟨sub_nonneg.mpr (le_min hp hq), sub_le_self _ (residualOverlap_nonneg p q s),
    min_le_right _ _⟩

end IdentityTesting
