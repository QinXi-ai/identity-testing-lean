import IdentityTesting.OverlapMoment
import IdentityTesting.GeneralAllocationBounds

/-! Finite truncated overlap moments and their exact countable interpretation. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators
open FiniteTesting

def finiteOverlapMoment {Ω : Type*} [Fintype Ω] (q : Probability Ω) (δ : ℝ) : ℝ :=
  ∑ i, min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ)

theorem overlapMoment_extendFiniteLaw {k : ℕ} (q : Probability (Fin k)) (δ : ℝ) :
    overlapMoment (extendFiniteLaw q) δ = finiteOverlapMoment q δ := by
  have hz : ∀ i, i ∉ Set.range (fun j : Fin k => j.val) →
      min ((extendFiniteLaw q).mass i)
        (((extendFiniteLaw q).mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) = 0 := by
    intro i hi
    have hn : ¬ i < k := fun h => hi ⟨⟨i, h⟩, rfl⟩
    rw [extendFiniteLaw_mass_of_not_lt q i hn]
    norm_num
  let g := fun i => min ((extendFiniteLaw q).mass i)
    (((extendFiniteLaw q).mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ)
  have hs : HasSum g (∑ j : Fin k, g j.val) :=
    (Fin.val_injective.hasSum_iff (f := g) (a := ∑ j : Fin k, g j.val) hz).mp
      (by simpa only [Function.comp_apply] using hasSum_fintype (fun j : Fin k => g j.val))
  simpa only [g, overlapMoment, finiteOverlapMoment, extendFiniteLaw_mass_val] using hs.tsum_eq

variable {Ω : Type*} [Fintype Ω]

theorem overlapTerm_nonneg (q : Probability Ω) (δ : ℝ) (i : Ω) :
    0 ≤ min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) :=
  le_min (q.nonneg i) (div_nonneg (Real.rpow_nonneg (q.nonneg i) _) (Real.sqrt_nonneg _))

theorem finiteOverlapMoment_nonneg (q : Probability Ω) (δ : ℝ) :
    0 ≤ finiteOverlapMoment q δ := Finset.sum_nonneg (fun i _ => overlapTerm_nonneg q δ i)

theorem finiteOverlapMoment_le_one (q : Probability Ω) (δ : ℝ) :
    finiteOverlapMoment q δ ≤ 1 := by
  exact (Finset.sum_le_sum (fun i _ => min_le_left (q.mass i) _)).trans_eq q.total

theorem overlapTerm_light {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (haδ : a ≤ δ) :
    min a (a ^ ((3 : ℝ) / 2) / Real.sqrt δ) = a ^ ((3 : ℝ) / 2) / Real.sqrt δ := by
  apply min_eq_right
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hδ)).mpr
  rw [allocation_three_halves_eq ha]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt haδ) ha

theorem mass_le_four_overlapTerm {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    (hlarge : δ / 16 < a) :
    a ≤ 4 * min a (a ^ ((3 : ℝ) / 2) / Real.sqrt δ) := by
  have hs : Real.sqrt δ ≤ 4 * Real.sqrt a := by
    have hsa := Real.sq_sqrt ha
    have hsd := Real.sq_sqrt hδ.le
    have h0 := Real.sqrt_nonneg a
    have h1 := Real.sqrt_nonneg δ
    nlinarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  apply le_min (by linarith)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hδ)).mpr
  rw [allocation_three_halves_eq ha]
  nlinarith only [mul_le_mul_of_nonneg_left hs ha]

open Classical
def momentRetained (q : Probability Ω) (δ : ℝ) : Finset Ω :=
  Finset.univ.filter (fun i => 0 < q.mass i ∧ q.mass i ≤ δ / 16)

theorem momentRetained_pos (q : Probability Ω) (δ : ℝ) {i : Ω}
    (hi : i ∈ momentRetained q δ) : 0 < q.mass i := (Finset.mem_filter.mp hi).2.1

theorem momentRetained_cap (q : Probability Ω) (δ : ℝ) {i : Ω}
    (hi : i ∈ momentRetained q δ) : q.mass i ≤ δ / 16 := (Finset.mem_filter.mp hi).2.2

theorem momentDeleted_mass_le (q : Probability Ω) (δ : ℝ) (hδ : 0 < δ) :
    (∑ i ∈ (momentRetained q δ)ᶜ, q.mass i) ≤ 4 * finiteOverlapMoment q δ := by
  calc
    _ ≤ ∑ i ∈ (momentRetained q δ)ᶜ,
        4 * min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : q.mass i = 0
      · rw [hz]
        norm_num
      · have hpos : 0 < q.mass i := lt_of_le_of_ne (q.nonneg i) (Ne.symm hz)
        have hl : δ / 16 < q.mass i := by
          by_contra hn
          exact (Finset.mem_compl.mp hi) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos, le_of_not_gt hn⟩)
        exact mass_le_four_overlapTerm (q.nonneg i) hδ hl
    _ ≤ ∑ i, 4 * min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
        mul_nonneg (by norm_num) (overlapTerm_nonneg q δ i))
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem momentRetained_moment_le (q : Probability Ω) (δ : ℝ) (hδ : 0 < δ) :
    (∑ i ∈ momentRetained q δ, (q.mass i) ^ ((3 : ℝ) / 2)) ≤
      Real.sqrt δ * finiteOverlapMoment q δ := by
  have hs := Real.sqrt_pos.mpr hδ
  calc
    _ = ∑ i ∈ momentRetained q δ,
        Real.sqrt δ * min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [overlapTerm_light (q.nonneg i) hδ (by have h := momentRetained_cap q δ hi; linarith)]
      field_simp
    _ ≤ ∑ i, Real.sqrt δ * min (q.mass i) ((q.mass i) ^ ((3 : ℝ) / 2) / Real.sqrt δ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
        mul_nonneg hs.le (overlapTerm_nonneg q δ i))
    _ = _ := by rw [← Finset.mul_sum]; rfl

end IdentityTesting
