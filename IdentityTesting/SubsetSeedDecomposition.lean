import IdentityTesting.SubprobabilityCells
import IdentityTesting.SeedSampleKernel
import IdentityTesting.SeedSupport

/-! Actual subset/exterior decomposition, including an empty compressed subset
and zero exterior mass. A specified point outside the subset provides a supported
dummy exterior law when its mixture weight is zero. -/

noncomputable section
namespace IdentityTesting.SubsetSeedCompression
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds MultiBinSeeds MultiBinExterior SeedExterior SeedSampleKernel

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def outsideMass (ν : Probability Ω) (S : Finset Ω) : ℝ :=
  ∑ x, if x ∈ S then 0 else ν.mass x

theorem outsideMass_nonneg (ν : Probability Ω) (S : Finset Ω) : 0 ≤ outsideMass ν S := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact le_rfl | exact ν.nonneg x

theorem mass_le_outsideMass (ν : Probability Ω) (S : Finset Ω) {x : Ω} (hx : x ∉ S) :
    ν.mass x ≤ outsideMass ν S := by
  apply le_trans (show ν.mass x = (if x ∈ S then 0 else ν.mass x) from (if_neg hx).symm).le
  apply Finset.single_le_sum (s := Finset.univ) (f := fun y => if y ∈ S then 0 else ν.mass y)
  · intro y _
    split_ifs <;> first | exact le_rfl | exact ν.nonneg y
  · exact Finset.mem_univ x

theorem outsideMass_add_subset (ν : Probability Ω) (S : Finset Ω) :
    outsideMass ν S + ∑ x ∈ S, ν.mass x = 1 := by
  have h : (∑ x, ((if x ∈ S then 0 else ν.mass x) +
      (if x ∈ S then ν.mass x else 0))) = ∑ x, ν.mass x := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [Finset.sum_add_distrib] at h
  have hi : (∑ x, if x ∈ S then ν.mass x else 0) = ∑ x ∈ S, ν.mass x := by simp
  rw [hi, ν.total] at h
  exact h

/-- Normalize the actual exterior when nonzero; otherwise use the specified
outside point. -/
def subsetExterior (ν : Probability Ω) (S : Finset Ω) (z : Ω) : Probability Ω :=
  if h : 0 < outsideMass ν S then {
    mass x := if x ∈ S then 0 else ν.mass x / outsideMass ν S
    nonneg x := by
      split_ifs
      · exact le_rfl
      · exact div_nonneg (ν.nonneg x) h.le
    total := by
      calc
        (∑ x, if x ∈ S then 0 else ν.mass x / outsideMass ν S) =
            (∑ x, if x ∈ S then 0 else ν.mass x) / outsideMass ν S := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> simp
        _ = 1 := div_self h.ne'
  } else pointLaw z

theorem subsetExterior_scaled (ν : Probability Ω) (S : Finset Ω) (z x : Ω) :
    outsideMass ν S * (subsetExterior ν S z).mass x =
      if x ∈ S then 0 else ν.mass x := by
  by_cases h : 0 < outsideMass ν S
  · simp only [subsetExterior, dif_pos h]
    split_ifs
    · simp only [mul_zero]
    · field_simp [h.ne']
  · have h0 : outsideMass ν S = 0 :=
      le_antisymm (le_of_not_gt h) (outsideMass_nonneg ν S)
    rw [h0, zero_mul]
    by_cases hx : x ∈ S
    · simp [hx]
    · rw [if_neg hx]
      exact (le_antisymm (by simpa only [h0] using mass_le_outsideMass ν S hx)
        (ν.nonneg x)).symm

theorem subsetExterior_zero (ν : Probability Ω) (S : Finset Ω) (z : Ω) (hz : z ∉ S)
    {x : Ω} (hx : x ∈ S) : (subsetExterior ν S z).mass x = 0 := by
  have hxz : x ≠ z := by
    intro h
    subst x
    exact hz hx
  by_cases h : 0 < outsideMass ν S
  · simp [subsetExterior, h, hx]
  · simp [subsetExterior, h, pointLaw_mass, hxz]

theorem subsetExterior_positive_outside (ν : Probability Ω) (S : Finset Ω)
    (z : Ω) (hz : z ∉ S) (x : Ω) (hx : 0 < (subsetExterior ν S z).mass x) : x ∉ S := by
  intro hmem
  rw [subsetExterior_zero ν S z hz hmem] at hx
  exact (lt_irrefl 0) hx

def subsetAtoms (q : Probability Ω) (S : Finset Ω) (i : S) : ℝ := q.mass i.val

omit [DecidableEq Ω] in
theorem subset_sum_scaled (q ν : Probability Ω) (S : Finset Ω) (f : ℝ)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x) :
    (∑ x ∈ S, ν.mass x) = f * ∑ i : S, subsetAtoms q S i := by
  calc
    _ = ∑ x ∈ S, f * q.mass x := Finset.sum_congr rfl hscale
    _ = _ := by simp only [subsetAtoms, Finset.sum_coe_sort, Finset.mul_sum]

theorem subset_scaled_le_one (q ν : Probability Ω) (S : Finset Ω) (f : ℝ)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x) :
    f * ∑ i : S, subsetAtoms q S i ≤ 1 := by
  have h := outsideMass_add_subset ν S
  rw [subset_sum_scaled q ν S f hscale] at h
  linarith [outsideMass_nonneg ν S]

def subsetCellWeights (q : Probability Ω) (S : Finset Ω) (j : S → ℕ)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1) :
    Probability (Option (OccupiedCells j)) :=
  scaledCellWeights (subsetAtoms q S) (fun i => q.nonneg i.val) j f hf ht

def subsetCellLaws (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) : OccupiedCells j → Probability Ω :=
  embeddedCellLaw (subsetAtoms q S) (fun i => hq i.val i.property) j Subtype.val

/-- This classifier depends only on the fixed subset and its cell partition. -/
def subsetClassify (S : Finset Ω) (j : S → ℕ) (x : Ω) : Option (OccupiedCells j) :=
  if hx : x ∈ S then some (cellOf j ⟨x, hx⟩) else none

omit [Fintype Ω] in
@[simp] theorem subsetClassify_val (S : Finset Ω) (j : S → ℕ) (i : S) :
    subsetClassify S j i.val = some (cellOf j i) := by
  simp [subsetClassify, i.property]

omit [Fintype Ω] in
theorem subsetClassify_outside (S : Finset Ω) (j : S → ℕ) {x : Ω} (hx : x ∉ S) :
    subsetClassify S j x = none := by simp [subsetClassify, hx]

theorem subsetCellLaws_support (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (l : OccupiedCells j) (x : Ω)
    (hx : 0 < (subsetCellLaws q S hq j l).mass x) : subsetClassify S j x = some l := by
  obtain ⟨i, hi, hc⟩ := embeddedCellLaw_positive_preimage (subsetAtoms q S)
    (fun i => hq i.val i.property) j Subtype.val l x hx
  rw [← hi, subsetClassify_val, hc]

theorem subsetExterior_classify (ν : Probability Ω) (S : Finset Ω) (z : Ω) (hz : z ∉ S)
    (j : S → ℕ) (x : Ω) (hx : 0 < (subsetExterior ν S z).mass x) :
    subsetClassify S j x = none :=
  subsetClassify_outside S j (subsetExterior_positive_outside ν S z hz x hx)

theorem subsetCellWeights_none (q ν : Probability Ω) (S : Finset Ω) (j : S → ℕ)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x) :
    (subsetCellWeights q S j f hf ht).mass none = outsideMass ν S := by
  rw [subsetCellWeights, scaledCellWeights_none]
  have h := outsideMass_add_subset ν S
  rw [subset_sum_scaled q ν S f hscale] at h
  linarith

omit [DecidableEq Ω] in
theorem subsetCellLaws_zero_outside (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (l : OccupiedCells j)
    {x : Ω} (hx : x ∉ S) : (subsetCellLaws q S hq j l).mass x = 0 := by
  apply mapLaw_mass_eq_zero_of_not_mem (cellLaw (subsetAtoms q S) _ j l) Subtype.val x
  intro i hi
  exact hx (hi ▸ i.property)

/-- Exact uncompressed decomposition of every compatible ν, using the same cell
weights and conditional laws. -/
theorem subsetReference_eq (q ν : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (f : ℝ) (hf : 0 ≤ f)
    (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x) (z : Ω) (hz : z ∉ S) :
    mixture (subsetCellWeights q S j f hf ht)
      (withExterior (subsetExterior ν S z) (subsetCellLaws q S hq j)) = ν := by
  apply probability_ext
  intro x
  simp only [mixture_mass, Fintype.sum_option, withExterior]
  by_cases hx : x ∈ S
  · rw [subsetExterior_zero ν S z hz hx, mul_zero, zero_add]
    have h := sum_scaled_embeddedCellLaw_mass (subsetAtoms q S)
      (fun i => hq i.val i.property) j Subtype.val Subtype.val_injective f ⟨x, hx⟩
    change (∑ l, (f * cellMass (subsetAtoms q S) j l) *
      (embeddedCellLaw (subsetAtoms q S) (fun i => hq i.val i.property) j Subtype.val l).mass x) =
        ν.mass x
    exact h.trans (hscale x hx).symm
  · have hzsum : (∑ l, (subsetCellWeights q S j f hf ht).mass (some l) *
        (subsetCellLaws q S hq j l).mass x) = 0 := by
      apply Finset.sum_eq_zero
      intro l _
      rw [subsetCellLaws_zero_outside q S hq j l hx, mul_zero]
    rw [hzsum, add_zero, subsetCellWeights_none q ν S j f hf ht hscale]
    simpa only [if_neg hx] using subsetExterior_scaled ν S z x

omit [DecidableEq Ω] in
theorem subsetPrior_seed_mem (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (m : OccupiedCells j → ℕ)
    (seed : SeedIndex m → Ω) (hs : 0 < (multiBinSeedPrior (subsetCellLaws q S hq j) m).mass seed)
    (l : SeedIndex m) : seed l ∈ S := by
  have hp := independentLaw_positive_coordinate
    (fun l : SeedIndex m => subsetCellLaws q S hq j l.1) seed hs l
  obtain ⟨i, hi, _⟩ := embeddedCellLaw_positive_preimage (subsetAtoms q S)
    (fun i => hq i.val i.property) j Subtype.val l.1 (seed l) hp
  exact hi ▸ i.property

/-- Positive prior-weight realizations keep every original exterior mass. -/
theorem subsetCompressed_outside (q ν : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (f : ℝ) (hf : 0 ≤ f)
    (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x)
    (z : Ω) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l) (seed : SeedIndex m → Ω)
    (hs : 0 < (multiBinSeedPrior (subsetCellLaws q S hq j) m).mass seed)
    {x : Ω} (hx : x ∉ S) :
    (multiBinExteriorLaw (subsetCellWeights q S j f hf ht) (subsetExterior ν S z) m hm seed).mass x =
      ν.mass x := by
  have hseed (l : SeedIndex m) : seed l ≠ x := by
    intro h
    exact hx (h ▸ subsetPrior_seed_mem q S hq j m seed hs l)
  have he (l : OccupiedCells j) :
      (empiricalLaw (hm l) (fun j => seed ⟨l, j⟩)).mass x = 0 := by
    rw [empiricalLaw_mass]
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (hseed ⟨l, j⟩)
  simp only [multiBinExteriorLaw, mixture_mass, Fintype.sum_option, withExterior, he, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [subsetCellWeights_none q ν S j f hf ht hscale]
  simpa only [if_neg hx] using subsetExterior_scaled ν S z x

def subsetSampleKernel (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ)
    (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l) (n : ℕ) :
    (Fin n → Ω) → Probability (Fin n → Ω) :=
  wholeSampleSeedKernel (subsetCellLaws q S hq j) (subsetClassify S j) id m hm n

omit [DecidableEq Ω] in
private theorem mapLaw_id_law (p : Probability Ω) : mapLaw p id = p := by
  exact probability_ext (mixture_pointLaw_mass p)

/-- The actual subset kernel is independent of ν, f, and the dummy point. -/
theorem subsetSampleKernel_productLaw (q ν : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (f : ℝ) (hf : 0 ≤ f)
    (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale : ∀ x ∈ S, ν.mass x = f * q.mass x) (z : Ω) (hz : z ∉ S)
    (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l) (n : ℕ) :
    mixture (productLaw ν n) (subsetSampleKernel q S hq j m hm n) =
      multiBinExteriorSampleMixture (subsetCellWeights q S j f hf ht) (subsetCellLaws q S hq j)
        (subsetExterior ν S z) m hm n := by
  have h := wholeSampleSeedKernel_reference (subsetCellWeights q S j f hf ht)
    (subsetCellLaws q S hq j) (subsetExterior ν S z) (subsetClassify S j) id m hm n
    (subsetCellLaws_support q S hq j) (subsetExterior_classify ν S z hz j)
  rw [subsetReference_eq q ν S hq j f hf ht hscale z hz, mapLaw_id_law] at h
  exact h

theorem subsetSampleKernel_family {A : Type*} [Fintype A] (θ : Probability A)
    (q : Probability Ω) (ν : A → Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (f : ℝ) (hf : 0 ≤ f)
    (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale : ∀ a x, x ∈ S → (ν a).mass x = f * q.mass x) (z : Ω) (hz : z ∉ S)
    (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l) (n : ℕ) :
    mixture (mixture θ (fun a => productLaw (ν a) n)) (subsetSampleKernel q S hq j m hm n) =
      mixture θ (fun a => multiBinExteriorSampleMixture (subsetCellWeights q S j f hf ht)
        (subsetCellLaws q S hq j) (subsetExterior (ν a) S z) m hm n) := by
  calc
    _ = mixture θ (fun a => mixture (productLaw (ν a) n)
      (subsetSampleKernel q S hq j m hm n)) := by
      apply probability_ext
      intro y
      exact mixture_kernel_mass θ _ (subsetSampleKernel q S hq j m hm n) y
    _ = _ := by
      apply congrArg (mixture θ)
      funext a
      exact subsetSampleKernel_productLaw q (ν a) S hq j f hf ht (hscale a) z hz m hm n

/-- All compatible input laws use the same constructed sample kernel. -/
theorem subsetCompression_family_tv_le {A : Type*} [Fintype A] (θ : Probability A)
    (q ν₀ : Probability Ω) (ν : A → Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (j : S → ℕ) (f : ℝ) (hf : 0 ≤ f)
    (ht : f * ∑ i : S, subsetAtoms q S i ≤ 1)
    (hscale₀ : ∀ x ∈ S, ν₀.mass x = f * q.mass x)
    (hscale : ∀ a x, x ∈ S → (ν a).mass x = f * q.mass x) (z : Ω) (hz : z ∉ S)
    (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l) (n : ℕ) :
    FiniteTesting.totalVariation
      (mixture θ (fun a => multiBinExteriorSampleMixture (subsetCellWeights q S j f hf ht)
        (subsetCellLaws q S hq j) (subsetExterior (ν a) S z) m hm n))
      (multiBinExteriorSampleMixture (subsetCellWeights q S j f hf ht) (subsetCellLaws q S hq j)
        (subsetExterior ν₀ S z) m hm n) ≤
      FiniteTesting.totalVariation (mixture θ (fun a => productLaw (ν a) n)) (productLaw ν₀ n) := by
  rw [← subsetSampleKernel_family θ q ν S hq j f hf ht hscale z hz m hm n,
    ← subsetSampleKernel_productLaw q ν₀ S hq j f hf ht hscale₀ z hz m hm n]
  exact totalVariation_kernel_le _ _ (subsetSampleKernel q S hq j m hm n)

end IdentityTesting.SubsetSeedCompression
