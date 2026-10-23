import IdentityTesting.SubprobabilityCells
import Mathlib.Data.Fintype.EquivFin

/-! An actual positive finite reference obtained by omitting zero masses. -/
noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
open Classical EmpiricalSeeds
variable {Ω : Type*} [Fintype Ω]

abbrev PositiveLabel (q : Probability Ω) := {i : Ω // 0 < q.mass i}

def positiveSupportLaw (q : Probability Ω) : Probability (PositiveLabel q) where
  mass i := q.mass i.val
  nonneg i := i.property.le
  total := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < q.mass i) q.mass
    have hz : (∑ i : {i : Ω // ¬ 0 < q.mass i}, q.mass i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact le_antisymm (le_of_not_gt i.property) (q.nonneg i)
    rw [hz, add_zero, q.total] at h
    exact h

def positiveEnumeration (q : Probability Ω) : Fin (Fintype.card (PositiveLabel q)) → Ω :=
  fun i => ((Fintype.equivFin (PositiveLabel q)).symm i).val

def positiveFiniteLaw (q : Probability Ω) : Probability (Fin (Fintype.card (PositiveLabel q))) :=
  mapLaw (positiveSupportLaw q) (Fintype.equivFin (PositiveLabel q))

theorem positiveEnumeration_injective (q : Probability Ω) :
    Function.Injective (positiveEnumeration q) :=
  Subtype.val_injective.comp (Fintype.equivFin (PositiveLabel q)).symm.injective

theorem positiveFiniteLaw_mass (q : Probability Ω) (i : Fin (Fintype.card (PositiveLabel q))) :
    (positiveFiniteLaw q).mass i = q.mass (positiveEnumeration q i) := by
  have h := mapLaw_mass_injective (positiveSupportLaw q) (Fintype.equivFin (PositiveLabel q))
    (Fintype.equivFin (PositiveLabel q)).injective ((Fintype.equivFin (PositiveLabel q)).symm i)
  simpa only [Equiv.apply_symm_apply] using h

theorem positiveFiniteLaw_pos (q : Probability Ω) (i : Fin (Fintype.card (PositiveLabel q))) :
    0 < (positiveFiniteLaw q).mass i := by
  rw [positiveFiniteLaw_mass]
  exact ((Fintype.equivFin (PositiveLabel q)).symm i).property

theorem mapLaw_positiveFiniteLaw (q : Probability Ω) :
    mapLaw (positiveFiniteLaw q) (positiveEnumeration q) = q := by
  apply probability_ext
  intro x
  by_cases hx : 0 < q.mass x
  · let i := (Fintype.equivFin (PositiveLabel q)) ⟨x, hx⟩
    have hi : positiveEnumeration q i = x := by simp only [positiveEnumeration, i, Equiv.symm_apply_apply]
    rw [← hi, mapLaw_mass_injective _ _ (positiveEnumeration_injective q), positiveFiniteLaw_mass]
  · have hx0 : q.mass x = 0 := le_antisymm (le_of_not_gt hx) (q.nonneg x)
    rw [mapLaw_mass_eq_zero_of_not_mem]
    · exact hx0.symm
    · intro i hi
      have hp := positiveFiniteLaw_pos q i
      rw [positiveFiniteLaw_mass, hi, hx0] at hp
      exact lt_irrefl 0 hp

theorem exists_positive_finite_representation (q : Probability Ω) :
    ∃ (k : ℕ) (p : Probability (Fin k)) (e : Fin k → Ω),
      Function.Injective e ∧ (∀ i, 0 < p.mass i) ∧
      (∀ i, p.mass i = q.mass (e i)) ∧ mapLaw p e = q :=
  ⟨_, positiveFiniteLaw q, positiveEnumeration q, positiveEnumeration_injective q,
    positiveFiniteLaw_pos q, positiveFiniteLaw_mass q, mapLaw_positiveFiniteLaw q⟩

end IdentityTesting.FiniteTesting
