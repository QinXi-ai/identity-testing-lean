import IdentityTesting.DyadicCells

/-! Actual cell weights for a scaled subprobability and conditional laws on an
ambient finite alphabet. The remaining mass is assigned to a fixed exterior. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

theorem mapLaw_mass_injective (p : Probability ι) (e : ι → Ω)
    (he : Function.Injective e) (i : ι) : (mapLaw p e).mass (e i) = p.mass i := by
  simp only [mapLaw_mass, he.eq_iff]
  simp

theorem mapLaw_mass_eq_zero_of_not_mem (p : Probability ι) (e : ι → Ω) (x : Ω)
    (hx : ∀ i, e i ≠ x) : (mapLaw p e).mass x = 0 := by
  simp only [mapLaw_mass, if_neg (hx _), Finset.sum_const_zero]

theorem mapLaw_positive_preimage (p : Probability ι) (e : ι → Ω) (x : Ω)
    (hx : 0 < (mapLaw p e).mass x) : ∃ i, e i = x ∧ 0 < p.mass i := by
  have hs : 0 < ∑ i, if e i = x then p.mass i else 0 := by
    simpa only [mapLaw_mass] using hx
  by_contra h
  have hn : ∀ i, e i = x → p.mass i ≤ 0 := by
    intro i hi
    exact le_of_not_gt (fun hp => h ⟨i, hi, hp⟩)
  have hz : (∑ i, if e i = x then p.mass i else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    split_ifs with hi
    · exact hn i hi
    · exact le_rfl
  exact (not_lt_of_ge hz) hs

def scaledCellWeights (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ι → ℕ)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i, a i ≤ 1) :
    Probability (Option (OccupiedCells j)) where
  mass l := match l with
    | none => 1 - f * ∑ i, a i
    | some l => f * cellMass a j l
  nonneg l := by
    cases l with
    | none => exact sub_nonneg.mpr ht
    | some l => exact mul_nonneg hf (cellMass_nonneg ha j l)
  total := by
    rw [Fintype.sum_option]
    simp only
    rw [← Finset.mul_sum, sum_cellMass]
    ring

@[simp] theorem scaledCellWeights_none (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ι → ℕ)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i, a i ≤ 1) :
    (scaledCellWeights a ha j f hf ht).mass none = 1 - f * ∑ i, a i := rfl

@[simp] theorem scaledCellWeights_some (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ι → ℕ)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i, a i ≤ 1) (l : OccupiedCells j) :
    (scaledCellWeights a ha j f hf ht).mass (some l) = f * cellMass a j l := rfl

def embeddedCellLaw (a : ι → ℝ) (ha : ∀ i, 0 < a i) (j : ι → ℕ)
    (e : ι → Ω) (l : OccupiedCells j) : Probability Ω :=
  mapLaw (cellLaw a ha j l) e

theorem embeddedCellLaw_positive_preimage (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (j : ι → ℕ) (e : ι → Ω) (l : OccupiedCells j) (x : Ω)
    (hx : 0 < (embeddedCellLaw a ha j e l).mass x) :
    ∃ i, e i = x ∧ cellOf j i = l := by
  obtain ⟨i, hi, hp⟩ := mapLaw_positive_preimage (cellLaw a ha j l) e x hx
  exact ⟨i, hi, (cellLaw_positive_iff a ha j l i).mp hp⟩

theorem embeddedCellLaw_mass (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (j : ι → ℕ) (e : ι → Ω) (he : Function.Injective e)
    (l : OccupiedCells j) (i : ι) :
    (embeddedCellLaw a ha j e l).mass (e i) =
      if cellOf j i = l then a i / cellMass a j l else 0 :=
  mapLaw_mass_injective (cellLaw a ha j l) e he i

/-- The actual weighted cell conditionals reproduce f times every original mass. -/
theorem sum_scaled_embeddedCellLaw_mass (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (j : ι → ℕ) (e : ι → Ω) (he : Function.Injective e) (f : ℝ) (i : ι) :
    (∑ l, (f * cellMass a j l) * (embeddedCellLaw a ha j e l).mass (e i)) = f * a i := by
  simp only [embeddedCellLaw_mass a ha j e he]
  calc
    _ = ∑ l : OccupiedCells j, if cellOf j i = l then f * a i else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases h : cellOf j i = l
      · simp only [h, ite_true]
        field_simp [(cellMass_pos ha j l).ne']
      · simp [h]
    _ = _ := by simp

end IdentityTesting.EmpiricalSeeds
