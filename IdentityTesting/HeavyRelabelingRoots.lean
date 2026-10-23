import IdentityTesting.HeavyFiniteBridge
import IdentityTesting.FiniteAllocationEmbedding

/-! # Heavy roots under an actual injective finite placement -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

open Classical FiniteTesting HeavySignedFamily

theorem largestMass_of_finite_embedding {m : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin m)) (e : Fin m → ℕ)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0) :
    largestMass q = largestMass (extendFiniteLaw p) := by
  apply le_antisymm
  · rw [largestMass_eq_selected]
    by_cases hn : largestIndex q ∈ Set.range e
    · obtain ⟨i, hi⟩ := hn
      rw [← hi, hmass, ← extendFiniteLaw_mass_val p i, largestMass_eq_selected]
      exact largestIndex_spec (extendFiniteLaw p) i.val
    · rw [hoff _ hn]
      exact (largestMass_pos (extendFiniteLaw p)).le
  · rw [largestMass_eq_selected (extendFiniteLaw p)]
    let n := largestIndex (extendFiniteLaw p)
    by_cases hn : n < m
    · have hv : (extendFiniteLaw p).mass n = p.mass ⟨n, hn⟩ := extendFiniteLaw_mass_val p ⟨n, hn⟩
      change (extendFiniteLaw p).mass n ≤ _
      rw [hv, ← hmass, largestMass_eq_selected]
      exact largestIndex_spec q _
    · change (extendFiniteLaw p).mass n ≤ _
      rw [extendFiniteLaw_mass_of_not_lt p n hn]
      exact (largestMass_pos q).le

theorem countableObjective_of_positive_vector_embedding {m : ℕ}
    (a : ℕ → ℝ) (b : Fin m → ℝ) (e : Fin m → ℕ)
    (he : Function.Injective e) (hmass : ∀ i, a (e i) = b i)
    (hoff : ∀ n, n ∉ Set.range e → a n = 0)
    {t : ℝ} (ht : 0 < t) (hb : ∀ i, 0 < b i)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    countableAllocationObjective a t u = allocationObjective t b (fun i => u (e i)) := by
  let f := fun n => a n * (u n / (u n + t ^ 2 * (a n) ^ 2)) ^ (1 / (4 : ℝ))
  have hz : ∀ n, n ∉ Set.range e → f n = 0 := by
    intro n hn
    simp only [f, hoff n hn, zero_mul]
  have hs : HasSum f (∑ i, f (e i)) :=
    (he.hasSum_iff (f := f) (a := ∑ i, f (e i)) hz).mp
      (by simpa only [Function.comp_apply] using hasSum_fintype (fun i => f (e i)))
  rw [allocationObjective_eq_rpow ht hb (fun i => hu (e i))]
  simpa only [countableAllocationObjective, f, hmass] using hs.tsum_eq

theorem allocationD_of_positive_vector_embedding {m : ℕ}
    (a : ℕ → ℝ) (b : Fin m → ℝ) (hb : ∀ i, 0 < b i)
    (e : Fin m → ℕ) (he : Function.Injective e) (hmass : ∀ i, a (e i) = b i)
    (hoff : ∀ n, n ∉ Set.range e → a n = 0) {t : ℝ} (ht : 0 < t) :
    allocationD a t = allocationD (extendFiniteVector b) t := by
  rw [allocationD_extendFiniteVector_eq_sSup ht hb]
  unfold allocationD
  apply congrArg sSup
  ext d
  constructor
  · rintro ⟨u, hu, hd⟩
    refine ⟨(fun i => u (e i)), allocationSimplex_restrict_embedding e he hu, ?_⟩
    exact hd.trans (countableObjective_of_positive_vector_embedding a b e he hmass hoff ht hb u hu.1)
  · rintro ⟨u, hu, hd⟩
    have hfeas := pushFiniteAllocation_feasible e he u hu
    refine ⟨pushFiniteAllocation e u, hfeas, ?_⟩
    rw [countableObjective_of_positive_vector_embedding a b e he hmass hoff ht hb _ hfeas.1]
    simpa only [pushFiniteAllocation_apply e he] using hd

theorem largestIndex_of_heavy_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin (k + 1)))
    (e : Fin (k + 1) → ℕ) (_he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (hR : tailTotal p ≤ (1 : ℝ) / 4) : largestIndex q = e 0 := by
  have ht := reference_head_tail p
  have hhead : (3 : ℝ) / 4 ≤ p.mass 0 := by linarith only [ht, hR]
  have hR0 : 0 ≤ tailTotal p := Finset.sum_nonneg (fun i _ => p.nonneg i.succ)
  have hfinite : ∀ i : Fin (k + 1), i ≠ 0 → p.mass i ≤ tailTotal p := by
    intro i
    refine Fin.cases (by intro h; exact False.elim (h rfl)) (fun j _ => ?_) i
    exact Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => p.nonneg l.succ) (Finset.mem_univ j)
  have hnonhead : ∀ n, n ≠ e 0 → q.mass n ≤ tailTotal p := by
    intro n hn
    by_cases hnmem : n ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hnmem
      rw [hmass]
      exact hfinite i (fun hi => hn (congrArg e hi))
    · rw [hoff n hnmem]
      exact hR0
  by_contra hne
  have hsmall := hnonhead (largestIndex q) hne
  have hlarge := largestIndex_spec q (e 0)
  rw [hmass] at hlarge
  linarith only [hsmall, hlarge, hhead, hR]

theorem tailMasses_of_heavy_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin (k + 1)))
    (e : Fin (k + 1) → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (hR : tailTotal p ≤ (1 : ℝ) / 4) :
    (∀ i : Fin k, tailMasses q (e i.succ) = p.mass i.succ) ∧
      (∀ n, n ∉ Set.range (fun i : Fin k => e i.succ) → tailMasses q n = 0) := by
  have hindex := largestIndex_of_heavy_finite_embedding q p e he hmass hoff hR
  constructor
  · intro i
    rw [tailMasses, hindex, if_neg (fun h => Fin.succ_ne_zero i (he h)), hmass]
  · intro n hn
    by_cases hn0 : n = e 0
    · simp only [tailMasses, hindex, hn0, ite_true]
    · rw [tailMasses, hindex, if_neg hn0]
      apply hoff n
      rintro ⟨i, hi⟩
      have hcases : i = 0 ∨ ∃ j : Fin k, i = j.succ := by
        refine Fin.cases (Or.inl rfl) (fun j => Or.inr ⟨j, rfl⟩) i
      rcases hcases with rfl | ⟨j, rfl⟩
      · exact hn0 hi.symm
      · exact hn ⟨j, hi⟩

theorem tailAllocationD_of_heavy_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin (k + 1))) (hp : ∀ i, 0 < p.mass i)
    (e : Fin (k + 1) → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (hR : tailTotal p ≤ (1 : ℝ) / 4) {t : ℝ} (ht : 0 < t) :
    allocationD (tailMasses q) t = allocationD (tailMasses (extendFiniteLaw p)) t := by
  obtain ⟨hm, hz⟩ := tailMasses_of_heavy_finite_embedding q p e he hmass hoff hR
  have hq := allocationD_of_positive_vector_embedding (tailMasses q) (fun i : Fin k => p.mass i.succ)
    (fun i => hp i.succ) (fun i : Fin k => e i.succ) (he.comp (Fin.succ_injective k)) hm hz ht
  have hp' := allocationD_of_positive_vector_embedding (extendFiniteTailVector (fun i : Fin k => p.mass i.succ))
    (fun i : Fin k => p.mass i.succ) (fun i => hp i.succ) (fun i : Fin k => i.succ.val)
    (Fin.val_injective.comp (Fin.succ_injective k))
    (extendFiniteTailVector_succ_val _) (extendFiniteTailVector_eq_zero_off _) ht
  rw [tailMasses_extendFiniteLaw_heavy p hR]
  exact hq.trans hp'.symm

theorem heavyRoot_of_heavy_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin (k + 1))) (hp : ∀ i, 0 < p.mass i)
    (e : Fin (k + 1) → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (hR : tailTotal p ≤ (1 : ℝ) / 4) (ε : ℝ) :
    heavyRoot q ε = heavyRoot (extendFiniteLaw p) ε := by
  have hm := largestMass_of_finite_embedding q p e hmass hoff
  unfold heavyRoot
  apply congrArg sInf
  ext t
  constructor <;> rintro ⟨ht, hd⟩
  · exact ⟨ht, by rwa [← hm, ← tailAllocationD_of_heavy_finite_embedding q p hp e he hmass hoff hR ht]⟩
  · exact ⟨ht, by rwa [hm, tailAllocationD_of_heavy_finite_embedding q p hp e he hmass hoff hR ht]⟩

theorem complexityScale_of_heavy_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin (k + 1))) (hp : ∀ i, 0 < p.mass i)
    (e : Fin (k + 1) → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (hR : tailTotal p < (1 : ℝ) / 4) (ε : ℝ) :
    complexityScale q ε = complexityScale (extendFiniteLaw p) ε := by
  have hm := largestMass_of_finite_embedding q p e hmass hoff
  have ht := reference_head_tail p
  have hheavy : (3 : ℝ) / 4 < largestMass (extendFiniteLaw p) := by
    rw [largestMass_extendFiniteLaw_heavy p hR.le]
    linarith only [ht, hR]
  unfold complexityScale
  rw [hm]
  dsimp only
  by_cases hε : ε = 1
  · simp [hε]
  by_cases hpoint : largestMass (extendFiniteLaw p) = 1
  · simp only [hε, hpoint, if_false, if_true]
  simp only [hε, hpoint, hheavy, if_false, if_true]
  rw [heavyRoot_of_heavy_finite_embedding q p hp e he hmass hoff hR.le ε,
    heavyRoot_of_heavy_finite_embedding q p hp e he hmass hoff hR.le
      (1 - largestMass (extendFiniteLaw p))]

end IdentityTesting
