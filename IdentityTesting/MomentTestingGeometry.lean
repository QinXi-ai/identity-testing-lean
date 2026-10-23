import IdentityTesting.FiniteOverlapMoment
import IdentityTesting.FiniteAllocationUpperOverlap
import IdentityTesting.EventChernoff
import IdentityTesting.CountablePooling

/-! Deterministic overlap geometry for the small-overlap testing upper bound. -/
noncomputable section
namespace IdentityTesting.MomentTesting
open scoped BigOperators
open Classical FiniteTesting FiniteAllocationUpper EventCounts CollisionTesting
variable {Ω : Type*} [Fintype Ω]

def heavyLabels (q : Probability Ω) (δ : ℝ) : Finset Ω :=
  Finset.univ.filter (fun i => δ ≤ q.mass i)

def lightLabels (q : Probability Ω) (δ : ℝ) : Finset Ω := (heavyLabels q δ)ᶜ

theorem finiteOverlapMoment_pos (q : Probability Ω) {δ : ℝ} (hδ : 0 < δ) :
    0 < finiteOverlapMoment q δ := by
  have hex : ∃ i, 0 < q.mass i := by
    by_contra hn
    have hsum : (∑ i, q.mass i) ≤ 0 := by
      exact Finset.sum_nonpos (fun i _ => le_of_not_gt (fun hi => hn ⟨i, hi⟩))
    rw [q.total] at hsum
    norm_num at hsum
  obtain ⟨i, hi⟩ := hex
  have hterm : 0 < min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) :=
    lt_min hi (div_pos (Real.rpow_pos_of_pos hi _) (Real.sqrt_pos.mpr hδ))
  exact hterm.trans_le (Finset.single_le_sum (fun j _ => overlapTerm_nonneg q δ j) (Finset.mem_univ i))

theorem overlapTerm_heavy {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hδa : δ ≤ a) :
    min a (a ^ ((3 : ℝ) / 2) / Real.sqrt δ) = a := by
  apply min_eq_left
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hδ)).mpr
  rw [allocation_three_halves_eq ha]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hδa) ha

theorem light_mass_lt (q : Probability Ω) (δ : ℝ) {i : Ω}
    (hi : i ∈ lightLabels q δ) : q.mass i < δ := by
  have hn := Finset.mem_compl.mp hi
  by_contra h
  exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_gt h⟩)

theorem moment_decomposition (q : Probability Ω) {δ : ℝ} (hδ : 0 < δ) :
    finiteOverlapMoment q δ = eventMass q (heavyLabels q δ) +
      weightedMass q q (lightLabels q δ) / Real.sqrt δ := by
  rw [finiteOverlapMoment, ← Finset.sum_add_sum_compl (heavyLabels q δ)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact overlapTerm_heavy (q.nonneg i) hδ (Finset.mem_filter.mp hi).2
  · rw [weightedMass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [overlapTerm_light (q.nonneg i) hδ (light_mass_lt q δ hi).le,
      allocation_three_halves_eq (q.nonneg i)]

theorem localOverlap_le_global (p q : Probability Ω) (L : Finset Ω) :
    localOverlap p q L ≤ 1 - FiniteTesting.totalVariation p q := by
  rw [finite_totalVariation_eq_one_sub_overlap]
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
    (fun i _ _ => le_min (p.nonneg i) (q.nonneg i))
  simpa only [sub_sub_cancel] using h

theorem heavy_eventMass_lt_of_alternative (p q : Probability Ω) {δ : ℝ}
    (hsep : 1 - δ < FiniteTesting.totalVariation p q) :
    eventMass p (heavyLabels q δ) < δ := by
  have hover : (∑ i, min (p.mass i) (q.mass i)) < δ := by
    rw [finite_totalVariation_eq_one_sub_overlap] at hsep
    linarith
  have hpoint (i : Ω) (hi : i ∈ heavyLabels q δ) : p.mass i < δ := by
    have hmin := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => min (p.mass j) (q.mass j))
      (fun j _ => le_min (p.nonneg j) (q.nonneg j)) (Finset.mem_univ i)
    have hqi := (Finset.mem_filter.mp hi).2
    by_contra hn
    have hδmin : δ ≤ min (p.mass i) (q.mass i) := le_min (le_of_not_gt hn) hqi
    linarith
  have heq : eventMass p (heavyLabels q δ) = localOverlap p q (heavyLabels q δ) := by
    unfold eventMass localOverlap
    apply Finset.sum_congr rfl
    intro i hi
    exact (min_eq_left ((hpoint i hi).le.trans (Finset.mem_filter.mp hi).2)).symm
  rw [heq]
  exact (localOverlap_le_global p q _).trans_lt (by linarith)

theorem light_collision_le (q : Probability Ω) {δ : ℝ} :
    collisionMass2 q (lightLabels q δ) ≤
      Real.sqrt δ * weightedMass q q (lightLabels q δ) := by
  rw [collisionMass2, weightedMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs := Real.sqrt_le_sqrt (light_mass_lt q δ hi).le
  have hmul := mul_le_mul_of_nonneg_right hs
    (mul_nonneg (q.nonneg i) (Real.sqrt_nonneg (q.mass i)))
  nlinarith only [hmul, Real.sq_sqrt (q.nonneg i)]

end IdentityTesting.MomentTesting
