import IdentityTesting.FinitePadding

/-! Exact masses after deleting a selected set into a zero-reference label. -/

noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
open Classical

variable {Ω : Type*} [Fintype Ω]

def deleteLaw (p : Probability Ω) (D : Finset Ω) (z : Ω) : Probability Ω :=
  mapLaw p (fun x => if x ∈ D then z else x)

theorem deleteLaw_mass_of_ne (p : Probability Ω) (D : Finset Ω) (z x : Ω) (hx : x ≠ z) :
    (deleteLaw p D z).mass x = if x ∈ D then 0 else p.mass x := by
  have hiff (y : Ω) : (if y ∈ D then z else y) = x ↔ y = x ∧ x ∉ D := by
    by_cases hy : y ∈ D
    · simp only [hy, ite_true]
      constructor
      · exact fun h => (hx h.symm).elim
      · rintro ⟨rfl, h⟩
        exact (h hy).elim
    · simp only [hy, ite_false]
      exact ⟨fun h => ⟨h, h ▸ hy⟩, And.left⟩
  simp only [deleteLaw, mapLaw_mass, hiff]
  by_cases h : x ∈ D <;> simp [h]

def liftedDeletionSet {k : ℕ} (D : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  D.image Fin.castSucc

theorem sum_liftedDeletionSet {k : ℕ} (D : Finset (Fin k)) (f : Fin (k + 1) → ℝ) :
    (∑ i ∈ liftedDeletionSet D, f i) = ∑ i ∈ D, f i.castSucc := by
  rw [liftedDeletionSet, Finset.sum_image]
  exact fun i _ j _ h => Fin.castSucc_injective k h

@[simp] theorem mem_liftedDeletionSet {k : ℕ} (D : Finset (Fin k)) (i : Fin k) :
    i.castSucc ∈ liftedDeletionSet D ↔ i ∈ D := by
  simp only [liftedDeletionSet, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact (Fin.castSucc_injective k hji) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem castSucc_ne_last {k : ℕ} (i : Fin k) : i.castSucc ≠ Fin.last k := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = k at hv
  exact (Nat.ne_of_lt i.isLt) hv

@[simp] theorem last_not_mem_liftedDeletionSet {k : ℕ} (D : Finset (Fin k)) :
    Fin.last k ∉ liftedDeletionSet D := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact castSucc_ne_last i hi

def deletePaddedLaw {k : ℕ} (p : Probability (Fin k)) (D : Finset (Fin k)) :
    Probability (Fin (k + 1)) :=
  deleteLaw (padFiniteLaw p) (liftedDeletionSet D) (Fin.last k)

@[simp] theorem deletePaddedLaw_mass_castSucc {k : ℕ}
    (p : Probability (Fin k)) (D : Finset (Fin k)) (i : Fin k) :
    (deletePaddedLaw p D).mass i.castSucc = if i ∈ D then 0 else p.mass i := by
  rw [deletePaddedLaw, deleteLaw_mass_of_ne _ _ _ _ (castSucc_ne_last i)]
  simp

theorem deletePaddedLaw_sample_tv_le {k : ℕ} (p : Probability (Fin k))
    (D : Finset (Fin k)) (n : ℕ) :
    totalVariation (productLaw (deletePaddedLaw p D) n) (productLaw (padFiniteLaw p) n) ≤
      (n : ℝ) * ∑ i ∈ D, p.mass i := by
  unfold deletePaddedLaw deleteLaw
  apply (totalVariation_productLaw_delete_le (padFiniteLaw p) (liftedDeletionSet D)
    (Fin.last k) n).trans
  have hsum : (∑ i ∈ liftedDeletionSet D, (padFiniteLaw p).mass i) = ∑ i ∈ D, p.mass i := by
    rw [liftedDeletionSet, Finset.sum_image]
    · simp
    · exact fun i _ j _ h => Fin.castSucc_injective k h
  rw [hsum]

end IdentityTesting.FiniteTesting
