import IdentityTesting.AllocationFiniteBridge
import IdentityTesting.PositiveSupport

/-! Allocation values and the original root are unchanged by an arbitrary
injective placement of a positive finite reference in the natural numbers. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators
open Classical FiniteTesting

def pushFiniteAllocation {k : ℕ} (e : Fin k → ℕ) (u : Fin k → ℝ) (n : ℕ) : ℝ :=
  ∑ i, if e i = n then u i else 0

theorem pushFiniteAllocation_apply {k : ℕ} (e : Fin k → ℕ) (he : Function.Injective e)
    (u : Fin k → ℝ) (i : Fin k) : pushFiniteAllocation e u (e i) = u i := by
  simp only [pushFiniteAllocation, he.eq_iff]
  simp

theorem pushFiniteAllocation_off {k : ℕ} (e : Fin k → ℕ) (u : Fin k → ℝ)
    (n : ℕ) (hn : n ∉ Set.range e) : pushFiniteAllocation e u n = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun hi => hn ⟨i, hi⟩)

theorem pushFiniteAllocation_feasible {k : ℕ} (e : Fin k → ℕ) (he : Function.Injective e)
    (u : Fin k → ℝ) (hu : u ∈ allocationSimplex (Fin k)) :
    AllocationFeasible (pushFiniteAllocation e u) := by
  have hs : HasSum (pushFiniteAllocation e u) (∑ i, u i) := by
    apply (he.hasSum_iff (f := pushFiniteAllocation e u) (a := ∑ i, u i)
      (pushFiniteAllocation_off e u)).mp
    have hc : pushFiniteAllocation e u ∘ e = u := by
      funext i
      exact pushFiniteAllocation_apply e he u i
    rw [hc]
    exact hasSum_fintype u
  refine ⟨?_, hs.summable, hs.tsum_eq.le.trans hu.2⟩
  intro n
  exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hu.1 i; exact le_rfl)

theorem allocationSimplex_restrict_embedding {k : ℕ} (e : Fin k → ℕ)
    (he : Function.Injective e) {u : ℕ → ℝ} (hu : AllocationFeasible u) :
    (fun i => u (e i)) ∈ allocationSimplex (Fin k) := by
  refine ⟨fun i => hu.1 (e i), ?_⟩
  have hsum : (∑ i : Fin k, u (e i)) = ∑ n ∈ Finset.univ.image e, u n := by
    rw [Finset.sum_image (fun i _ j _ h => he h)]
  rw [hsum]
  exact (hu.2.1.sum_le_tsum _ (fun n _ => hu.1 n)).trans hu.2.2

theorem countableObjective_of_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k)) (e : Fin k → ℕ)
    (he : Function.Injective e) (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (t : ℝ) (ht : 0 < t) (hp : ∀ i, 0 < p.mass i)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    countableAllocationObjective q.mass t u = allocationObjective t p.mass (fun i => u (e i)) := by
  let f := fun n => q.mass n * (u n / (u n + t ^ 2 * (q.mass n) ^ 2)) ^ (1 / (4 : ℝ))
  have hz : ∀ n, n ∉ Set.range e → f n = 0 := by
    intro n hn
    simp only [f, hoff n hn, zero_mul]
  have hs : HasSum f (∑ i, f (e i)) :=
    (he.hasSum_iff (f := f) (a := ∑ i, f (e i)) hz).mp
      (by simpa only [Function.comp_apply] using hasSum_fintype (fun i => f (e i)))
  rw [allocationObjective_eq_rpow ht hp (fun i => hu (e i))]
  simpa only [countableAllocationObjective, f, hmass] using hs.tsum_eq

theorem allocationD_of_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k)) (hp : ∀ i, 0 < p.mass i)
    (e : Fin k → ℕ) (he : Function.Injective e) (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0) (t : ℝ) (ht : 0 < t) :
    allocationD q.mass t = allocationD (extendFiniteLaw p).mass t := by
  rw [← extendFiniteVector_probability_mass p, allocationD_extendFiniteVector_eq_sSup ht hp]
  unfold allocationD
  apply congrArg sSup
  ext d
  constructor
  · rintro ⟨u, hu, hd⟩
    refine ⟨(fun i => u (e i)), allocationSimplex_restrict_embedding e he hu, ?_⟩
    exact hd.trans (countableObjective_of_finite_embedding q p e he hmass hoff t ht hp u hu.1)
  · rintro ⟨u, hu, hd⟩
    have hfeas := pushFiniteAllocation_feasible e he u hu
    refine ⟨pushFiniteAllocation e u, hfeas, ?_⟩
    rw [countableObjective_of_finite_embedding q p e he hmass hoff t ht hp _ hfeas.1]
    simpa only [pushFiniteAllocation_apply e he] using hd

theorem allocationRoot_of_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k)) (hp : ∀ i, 0 < p.mass i)
    (e : Fin k → ℕ) (he : Function.Injective e) (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0) (ε : ℝ) :
    allocationRoot q ε = allocationRoot (extendFiniteLaw p) ε := by
  unfold allocationRoot
  apply congrArg sInf
  ext t
  constructor <;> rintro ⟨ht, hd⟩
  · exact ⟨ht, by rwa [← allocationD_of_finite_embedding q p hp e he hmass hoff t ht]⟩
  · exact ⟨ht, by rwa [allocationD_of_finite_embedding q p hp e he hmass hoff t ht]⟩

end IdentityTesting
