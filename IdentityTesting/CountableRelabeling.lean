import IdentityTesting.CountableEmbedding
import IdentityTesting.LargestAtom

/-! Countable relabeling invariance of the actual manuscript functionals.
For tied largest atoms, a mass-preserving swap aligns the selected indices. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem allocationFeasible_comp_equiv_iff (e : ℕ ≃ ℕ) (u : ℕ → ℝ) :
    AllocationFeasible (u ∘ e) ↔ AllocationFeasible u := by
  constructor
  · rintro ⟨hu, hs, ht⟩
    refine ⟨fun i => ?_, e.summable_iff.mp hs, ?_⟩
    · simpa only [Function.comp_apply, e.apply_symm_apply] using hu (e.symm i)
    · simpa only [Function.comp_apply, e.tsum_eq] using ht
  · rintro ⟨hu, hs, ht⟩
    refine ⟨fun i => hu (e i), e.summable_iff.mpr hs, ?_⟩
    simpa only [Function.comp_apply, e.tsum_eq] using ht

theorem countableAllocationObjective_comp_equiv (e : ℕ ≃ ℕ)
    (a : ℕ → ℝ) (t : ℝ) (u : ℕ → ℝ) :
    countableAllocationObjective (a ∘ e) t (u ∘ e) =
      countableAllocationObjective a t u := by
  unfold countableAllocationObjective
  exact e.tsum_eq (fun i => a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ))

theorem allocationD_comp_equiv (e : ℕ ≃ ℕ) (a : ℕ → ℝ) (t : ℝ) :
    allocationD (a ∘ e) t = allocationD a t := by
  unfold allocationD
  apply congrArg sSup
  ext d
  constructor
  · rintro ⟨u, hu, hd⟩
    refine ⟨u ∘ e.symm, (allocationFeasible_comp_equiv_iff e.symm u).mpr hu, ?_⟩
    have hid := countableAllocationObjective_comp_equiv e a t (u ∘ e.symm)
    have hid' : countableAllocationObjective (a ∘ e) t u =
        countableAllocationObjective a t (u ∘ e.symm) := by
      simpa only [Function.comp_def, e.symm_apply_apply] using hid
    exact hd.trans hid'
  · rintro ⟨u, hu, hd⟩
    refine ⟨u ∘ e, (allocationFeasible_comp_equiv_iff e u).mpr hu, ?_⟩
    exact hd.trans (countableAllocationObjective_comp_equiv e a t u).symm

theorem allocationD_of_countable_equiv (a b : ℕ → ℝ) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, a (e i) = b i) (t : ℝ) : allocationD a t = allocationD b t := by
  have hid : a ∘ e = b := funext hmass
  rw [← hid, allocationD_comp_equiv]

theorem overlapMoment_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (δ : ℝ) :
    overlapMoment p δ = overlapMoment q δ := by
  unfold overlapMoment
  rw [← e.tsum_eq (fun i => min (p.mass i) (p.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ))]
  simp only [hmass]

theorem largestMass_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) : largestMass p = largestMass q := by
  unfold largestMass
  apply congrArg sSup
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨e.symm i, ?_⟩
    simpa only [e.apply_symm_apply] using (hmass (e.symm i)).symm
  · rintro ⟨i, rfl⟩
    exact ⟨e i, hmass i⟩

theorem allocationRoot_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (η : ℝ) :
    allocationRoot p η = allocationRoot q η := by
  simp only [allocationRoot, allocationD_of_countable_equiv p.mass q.mass e hmass]

/-- The original permutation need not preserve the least maximizing index.
A swap of equal-mass atoms produces a permutation that does. -/
theorem exists_countable_equiv_aligning_largest (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) :
    ∃ f : ℕ ≃ ℕ, (∀ i, p.mass (f i) = q.mass i) ∧
      f (largestIndex q) = largestIndex p := by
  let a := e.symm (largestIndex p)
  let b := largestIndex q
  have hab : q.mass a = q.mass b := by
    calc
      q.mass a = p.mass (largestIndex p) := by
        simpa only [a, e.apply_symm_apply] using (hmass a).symm
      _ = largestMass p := (largestMass_eq_selected p).symm
      _ = largestMass q := largestMass_of_countable_equiv p q e hmass
      _ = q.mass b := largestMass_eq_selected q
  have hswap (i : ℕ) : q.mass (Equiv.swap a b i) = q.mass i := by
    by_cases hia : i = a
    · subst i
      simpa only [Equiv.swap_apply_left] using hab.symm
    · by_cases hib : i = b
      · subst i
        simpa only [Equiv.swap_apply_right] using hab
      · simp only [Equiv.swap_apply_def, hia, hib, if_false]
  refine ⟨(Equiv.swap a b).trans e, ?_, ?_⟩
  · intro i
    change p.mass (e (Equiv.swap a b i)) = q.mass i
    rw [hmass, hswap]
  · change e (Equiv.swap a b b) = largestIndex p
    rw [Equiv.swap_apply_right]
    exact e.apply_symm_apply _

theorem tailAllocationD_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (t : ℝ) :
    allocationD (tailMasses p) t = allocationD (tailMasses q) t := by
  obtain ⟨f, hf, hindex⟩ := exists_countable_equiv_aligning_largest p q e hmass
  apply allocationD_of_countable_equiv _ _ f _ t
  intro i
  have hi : f i = largestIndex p ↔ i = largestIndex q := by
    rw [← hindex, f.injective.eq_iff]
  simp only [tailMasses, hi, hf]

theorem heavyRoot_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (η : ℝ) :
    heavyRoot p η = heavyRoot q η := by
  simp only [heavyRoot, tailAllocationD_of_countable_equiv p q e hmass,
    largestMass_of_countable_equiv p q e hmass]

theorem complexityScale_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (ε : ℝ) :
    complexityScale p ε = complexityScale q ε := by
  simp only [complexityScale, largestMass_of_countable_equiv p q e hmass,
    allocationRoot_of_countable_equiv p q e hmass,
    heavyRoot_of_countable_equiv p q e hmass,
    overlapMoment_of_countable_equiv p q e hmass]

theorem roundedScale_of_countable_equiv (p q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (hmass : ∀ i, p.mass (e i) = q.mass i) (ε : ℝ) :
    roundedScale p ε = roundedScale q ε := by
  simp only [roundedScale, complexityScale_of_countable_equiv p q e hmass]

/-- Actual relabeling of every countable law, via the existing `injectLaw`. -/
theorem countable_relabeling_functionals (q : DiscreteLaw) (e : ℕ ≃ ℕ)
    (t δ η ε : ℝ) :
    let p := injectLaw e e.injective q
    allocationD p.mass t = allocationD q.mass t ∧
      overlapMoment p δ = overlapMoment q δ ∧
      largestMass p = largestMass q ∧
      allocationRoot p η = allocationRoot q η ∧
      heavyRoot p η = heavyRoot q η ∧
      complexityScale p ε = complexityScale q ε ∧
      roundedScale p ε = roundedScale q ε := by
  let p := injectLaw e e.injective q
  have hmass (i : ℕ) : p.mass (e i) = q.mass i := injectMass_apply e e.injective q i
  exact ⟨allocationD_of_countable_equiv p.mass q.mass e hmass t,
    overlapMoment_of_countable_equiv p q e hmass δ,
    largestMass_of_countable_equiv p q e hmass,
    allocationRoot_of_countable_equiv p q e hmass η,
    heavyRoot_of_countable_equiv p q e hmass η,
    complexityScale_of_countable_equiv p q e hmass ε,
    roundedScale_of_countable_equiv p q e hmass ε⟩

end IdentityTesting
