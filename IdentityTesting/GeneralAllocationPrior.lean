import IdentityTesting.GeneralAllocationLowerBound

/-! The strict allocation prior constructed directly from the reference and radius. -/
noncomputable section
namespace IdentityTesting.GeneralLowerGeometry
open scoped BigOperators
open FiniteTesting

theorem exists_general_allocation_root_prior {k : ℕ}
    (q : Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    (hcap : ∀ i, q.mass i ≤ (4 : ℝ) / 5)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn0 : 0 < n) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) *
      allocationRoot (extendFiniteLaw q) ε) :
    ∃ (I : Type) (_ : Fintype I) (ω : Probability I)
      (P : I → Probability (Fin (k + 1))),
      (∀ i, 0 < ω.mass i → ε < FiniteTesting.totalVariation (P i) (padFiniteLaw q)) ∧
      FiniteTesting.totalVariation (mixture ω (fun i => productLaw (P i) n))
        (productLaw (padFiniteLaw q) n) < 1 / 10000 := by
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, _⟩ :=
    exists_finite_allocation_coordinates_at_root q hq hε0 hε1
  apply exists_general_allocation_prior q x (allocationRoot (extendFiniteLaw q) ε) ε
    hT hq hx hcap ?_ hbudget hsum n hn0 hn
  intro i j hij
  exact (allocation_stationary_geometry (hq j) hβ (hx i).1 (hx i).2
    (hx j).1 (hx j).2 hij (hstationary i) (hstationary j)).2

end IdentityTesting.GeneralLowerGeometry
