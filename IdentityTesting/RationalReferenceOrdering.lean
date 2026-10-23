import IdentityTesting.RationalMomentInterval
import IdentityTesting.HeavyRelabelingRoots
import IdentityTesting.HeavyRootOracleGeometry

/-! Executable rational maximum selection and head-first permutation, together
with invariance and tail bridges for the original statistical functional. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def rationalMaxValue {k : ℕ} (q : Fin (k + 1) → ℚ) : ℚ :=
  (Finset.univ.image q).max' (Finset.univ_nonempty.image q)

theorem rationalMaxValue_attained {k : ℕ} (q : Fin (k + 1) → ℚ) :
    ∃ i, q i = rationalMaxValue q := by
  have h := Finset.max'_mem (Finset.univ.image q) (Finset.univ_nonempty.image q)
  rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

def rationalMaxIndex {k : ℕ} (q : Fin (k + 1) → ℚ) : Fin (k + 1) :=
  (Finset.univ.filter (fun i => q i = rationalMaxValue q)).min' (by
    obtain ⟨i, hi⟩ := rationalMaxValue_attained q
    exact ⟨i, by simp [hi]⟩)

theorem rationalMaxIndex_value {k : ℕ} (q : Fin (k + 1) → ℚ) :
    q (rationalMaxIndex q) = rationalMaxValue q := by
  have h := Finset.min'_mem (Finset.univ.filter (fun i => q i = rationalMaxValue q))
    (by obtain ⟨i, hi⟩ := rationalMaxValue_attained q; exact ⟨i, by simp [hi]⟩)
  exact (Finset.mem_filter.mp h).2

theorem rationalMaxValue_upper {k : ℕ} (q : Fin (k + 1) → ℚ) (i : Fin (k + 1)) :
    q i ≤ rationalMaxValue q :=
  Finset.le_max' (Finset.univ.image q) (q i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

def rationalHeadSwap {k : ℕ} (q : Fin (k + 1) → ℚ) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.swap 0 (rationalMaxIndex q)

def rationalHeadFirst {k : ℕ} (q : Fin (k + 1) → ℚ) (i : Fin (k + 1)) : ℚ :=
  q (rationalHeadSwap q i)

def rationalTail {k : ℕ} (q : Fin (k + 1) → ℚ) (i : Fin k) : ℚ :=
  rationalHeadFirst q i.succ

theorem rationalHeadFirst_head {k : ℕ} (q : Fin (k + 1) → ℚ) :
    rationalHeadFirst q 0 = rationalMaxValue q := by
  simp only [rationalHeadFirst, rationalHeadSwap, Equiv.swap_apply_left]
  exact rationalMaxIndex_value q

theorem rationalHeadFirst_pos {k : ℕ} (q : Fin (k + 1) → ℚ) (hq : ∀ i, 0 < q i) :
    ∀ i, 0 < rationalHeadFirst q i := fun i => hq (rationalHeadSwap q i)

theorem rationalHeadFirst_sum {k : ℕ} (q : Fin (k + 1) → ℚ) :
    ∑ i, rationalHeadFirst q i = ∑ i, q i := Equiv.sum_comp (rationalHeadSwap q) q

theorem rationalHeadFirst_max {k : ℕ} (q : Fin (k + 1) → ℚ) (i : Fin (k + 1)) :
    rationalHeadFirst q i ≤ rationalHeadFirst q 0 := by
  rw [rationalHeadFirst_head]
  exact rationalMaxValue_upper q _

theorem rationalTail_pos {k : ℕ} (q : Fin (k + 1) → ℚ) (hq : ∀ i, 0 < q i) :
    ∀ i, 0 < rationalTail q i := fun i => rationalHeadFirst_pos q hq i.succ

theorem rationalTail_sum {k : ℕ} (q : Fin (k + 1) → ℚ) (hs : ∑ i, q i = 1) :
    ∑ i, rationalTail q i = 1 - rationalHeadFirst q 0 := by
  have h := (rationalHeadFirst_sum q).trans hs
  rw [Fin.sum_univ_succ] at h
  change rationalHeadFirst q 0 + (∑ i, rationalTail q i) = 1 at h
  linarith

noncomputable section
open FiniteTesting HeavySignedFamily

def rationalHeadFirstLaw {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) : Probability (Fin (k + 1)) :=
  rationalFiniteLaw (rationalHeadFirst q) (fun i => (rationalHeadFirst_pos q hq i).le)
    ((rationalHeadFirst_sum q).trans hs)

theorem rationalHeadFirstLaw_pos {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) :
    ∀ i, 0 < (rationalHeadFirstLaw q hq hs).mass i := by
  intro i
  change (0 : ℝ) < (rationalHeadFirst q i : ℝ)
  exact_mod_cast rationalHeadFirst_pos q hq i

theorem rationalHeadEmbedding_mass {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (i : Fin (k + 1)) :
    (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)).mass
      (rationalHeadSwap q i).val = (rationalHeadFirstLaw q hq hs).mass i := by
  rw [extendFiniteLaw_mass_val]
  rfl

theorem rationalHeadEmbedding_off {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (n : ℕ)
    (hn : n ∉ Set.range (fun i => (rationalHeadSwap q i).val)) :
    (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)).mass n = 0 := by
  apply extendFiniteLaw_mass_of_not_lt
  intro h
  apply hn
  refine ⟨(rationalHeadSwap q).symm ⟨n, h⟩, ?_⟩
  simp

theorem rationalHeadFirst_largestMass {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) :
    largestMass (extendFiniteLaw (rationalHeadFirstLaw q hq hs)) = rationalHeadFirst q 0 := by
  let p := rationalHeadFirstLaw q hq hs
  have hmax : ∀ n, (extendFiniteLaw p).mass n ≤ (rationalHeadFirst q 0 : ℝ) := by
    intro n
    by_cases hn : n < k + 1
    · rw [show (extendFiniteLaw p).mass n = p.mass ⟨n, hn⟩ from extendFiniteLaw_mass_val p ⟨n, hn⟩]
      change (rationalHeadFirst q ⟨n, hn⟩ : ℝ) ≤ (rationalHeadFirst q 0 : ℝ)
      exact_mod_cast rationalHeadFirst_max q ⟨n, hn⟩
    · rw [extendFiniteLaw_mass_of_not_lt p n hn]
      exact (rationalHeadFirstLaw_pos q hq hs 0).le
  apply le_antisymm
  · rw [largestMass_eq_selected]
    exact hmax _
  · have h := largestIndex_spec (extendFiniteLaw p) (0 : Fin (k + 1)).val
    rw [extendFiniteLaw_mass_val, ← largestMass_eq_selected] at h
    exact h

theorem rationalOriginal_largestMass {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) :
    largestMass (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) =
      rationalHeadFirst q 0 := by
  rw [largestMass_of_finite_embedding _ (rationalHeadFirstLaw q hq hs)
    (fun i => (rationalHeadSwap q i).val)
    (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs)]
  exact rationalHeadFirst_largestMass q hq hs

theorem rationalHeadFirst_overlapMoment {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (δ : ℝ) :
    overlapMoment (extendFiniteLaw (rationalHeadFirstLaw q hq hs)) δ =
      overlapMoment (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) δ := by
  rw [overlapMoment_extendFiniteLaw, overlapMoment_extendFiniteLaw]
  exact Equiv.sum_comp (rationalHeadSwap q) (fun i => min (q i : ℝ) ((q i : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt δ))

theorem rationalHeadFirst_allocationRoot {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (ε : ℝ) :
    allocationRoot (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) ε =
      allocationRoot (extendFiniteLaw (rationalHeadFirstLaw q hq hs)) ε :=
  allocationRoot_of_finite_embedding _ _ (rationalHeadFirstLaw_pos q hq hs)
    (fun i => (rationalHeadSwap q i).val) (Fin.val_injective.comp (rationalHeadSwap q).injective)
    (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs) ε

theorem rationalHeadFirst_tailTotal {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) :
    tailTotal (rationalHeadFirstLaw q hq hs) = 1 - (rationalHeadFirst q 0 : ℝ) := by
  have h := reference_head_tail (rationalHeadFirstLaw q hq hs)
  change (rationalHeadFirst q 0 : ℝ) + tailTotal (rationalHeadFirstLaw q hq hs) = 1 at h
  linarith

theorem rationalHeadFirst_complexityScale {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (ε : ℝ) :
    complexityScale (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) ε =
      complexityScale (extendFiniteLaw (rationalHeadFirstLaw q hq hs)) ε := by
  by_cases hh : (3 / 4 : ℝ) < rationalHeadFirst q 0
  · apply complexityScale_of_heavy_finite_embedding _ _ (rationalHeadFirstLaw_pos q hq hs)
      (fun i => (rationalHeadSwap q i).val) (Fin.val_injective.comp (rationalHeadSwap q).injective)
      (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs)
    rw [rationalHeadFirst_tailTotal]
    linarith
  · unfold complexityScale
    rw [rationalOriginal_largestMass q hq hs, rationalHeadFirst_largestMass q hq hs]
    simp only [hh, if_false]
    rw [rationalHeadFirst_allocationRoot q hq hs ε, rationalHeadFirst_overlapMoment q hq hs (1 - ε)]

theorem rationalHeadFirst_tailMasses {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0) :
    tailMasses (extendFiniteLaw (rationalHeadFirstLaw q hq hs)) =
      extendFiniteTailVector (fun i => (rationalTail q i : ℝ)) := by
  apply tailMasses_extendFiniteLaw_heavy
  rw [rationalHeadFirst_tailTotal]
  linarith

theorem rationalHeadFirst_tailAllocationD {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0)
    {t : ℝ} (ht : 0 < t) :
    allocationD (tailMasses (extendFiniteLaw (rationalHeadFirstLaw q hq hs))) t =
      allocationD (extendFiniteVector (fun i => (rationalTail q i : ℝ))) t := by
  rw [rationalHeadFirst_tailMasses q hq hs hh]
  exact allocationD_of_positive_vector_embedding _ _
    (fun i => by exact_mod_cast rationalTail_pos q hq i)
    (fun i : Fin k => i.succ.val) (Fin.val_injective.comp (Fin.succ_injective k))
    (extendFiniteTailVector_succ_val _) (extendFiniteTailVector_eq_zero_off _) ht

theorem rationalHeadFirst_heavyRoot {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0) (ε : ℝ) :
    heavyRoot (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) ε =
      finiteHeavyRoot (fun i => (rationalTail q i : ℝ)) ε := by
  have hR : tailTotal (rationalHeadFirstLaw q hq hs) ≤ (1 : ℝ) / 4 := by
    rw [rationalHeadFirst_tailTotal]
    linarith
  rw [heavyRoot_of_heavy_finite_embedding _ _ (rationalHeadFirstLaw_pos q hq hs)
    (fun i => (rationalHeadSwap q i).val) (Fin.val_injective.comp (rationalHeadSwap q).injective)
    (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs) hR ε]
  unfold heavyRoot finiteHeavyRoot
  apply congrArg sInf
  ext t
  have hsum : (∑ i, (rationalTail q i : ℝ)) = 1 - (rationalHeadFirst q 0 : ℝ) := by
    exact_mod_cast rationalTail_sum q hs
  constructor <;> rintro ⟨ht, hd⟩
  · refine ⟨ht, ?_⟩
    simpa only [finiteHeavyFunction, rationalHeadFirst_largestMass,
      rationalHeadFirst_tailAllocationD q hq hs hh ht, hsum] using hd
  · refine ⟨ht, ?_⟩
    simpa only [finiteHeavyFunction, rationalHeadFirst_largestMass,
      rationalHeadFirst_tailAllocationD q hq hs hh ht, hsum] using hd

theorem rationalOriginal_tailAllocationD {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0)
    {t : ℝ} (ht : 0 < t) :
    allocationD (tailMasses (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs))) t =
      allocationD (extendFiniteVector (fun i => (rationalTail q i : ℝ))) t := by
  have hR : tailTotal (rationalHeadFirstLaw q hq hs) ≤ (1 : ℝ) / 4 := by
    rw [rationalHeadFirst_tailTotal]
    linarith
  rw [tailAllocationD_of_heavy_finite_embedding _ _ (rationalHeadFirstLaw_pos q hq hs)
    (fun i => (rationalHeadSwap q i).val) (Fin.val_injective.comp (rationalHeadSwap q).injective)
    (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs) hR ht]
  exact rationalHeadFirst_tailAllocationD q hq hs hh ht

theorem rationalOriginal_largestIndex_heavy {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℝ) ≤ rationalHeadFirst q 0) :
    largestIndex (extendFiniteLaw (rationalFiniteLaw q (fun i => (hq i).le) hs)) =
      (rationalMaxIndex q).val := by
  have hR : tailTotal (rationalHeadFirstLaw q hq hs) ≤ (1 : ℝ) / 4 := by
    rw [rationalHeadFirst_tailTotal]
    linarith
  have h := largestIndex_of_heavy_finite_embedding _ (rationalHeadFirstLaw q hq hs)
    (fun i => (rationalHeadSwap q i).val) (Fin.val_injective.comp (rationalHeadSwap q).injective)
    (rationalHeadEmbedding_mass q hq hs) (rationalHeadEmbedding_off q hq hs) hR
  simpa only [rationalHeadSwap, Equiv.swap_apply_left] using h

theorem rationalHeadFirst_heavy_strict_max {k : ℕ} (q : Fin (k + 1) → ℚ)
    (hq : ∀ i, 0 < q i) (hs : ∑ i, q i = 1) (hh : (3 / 4 : ℚ) ≤ rationalHeadFirst q 0)
    (i : Fin (k + 1)) (hi : i ≠ 0) : rationalHeadFirst q i < rationalHeadFirst q 0 := by
  revert hi
  refine Fin.cases (by simp) (fun j _ => ?_) i
  have hj : rationalTail q j ≤ ∑ l, rationalTail q l :=
    Finset.single_le_sum (fun l _ => (rationalTail_pos q hq l).le) (Finset.mem_univ j)
  rw [rationalTail_sum q hs] at hj
  change rationalHeadFirst q j.succ ≤ 1 - rationalHeadFirst q 0 at hj
  linarith

end
end IdentityTesting.RationalComputation
