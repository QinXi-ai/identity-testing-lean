import IdentityTesting.AllocationFiniteBridge
import IdentityTesting.HeavyRoots
import IdentityTesting.HeavySignedFamily

/-! # Actual finite tail optimizers at the original countable heavy root -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

open FiniteTesting HeavySignedFamily

variable {k : ℕ}

def extendFiniteTailVector (a : Fin k → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => extendFiniteVector a n

@[simp] theorem extendFiniteTailVector_zero (a : Fin k → ℝ) :
    extendFiniteTailVector a 0 = 0 := rfl

@[simp] theorem extendFiniteTailVector_succ_val (a : Fin k → ℝ) (i : Fin k) :
    extendFiniteTailVector a i.succ.val = a i := by
  change extendFiniteVector a i.val = a i
  exact extendFiniteVector_val a i

private theorem tailLabel_injective : Function.Injective (fun i : Fin k => i.succ.val) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel hij

private theorem tail_hasSum (f : ℕ → ℝ)
    (hoff : ∀ n, n ∉ Set.range (fun i : Fin k => i.succ.val) → f n = 0) :
    HasSum f (∑ i : Fin k, f i.succ.val) := by
  have hf : HasSum (f ∘ (fun i : Fin k => i.succ.val)) (∑ i : Fin k, f i.succ.val) := by
    simpa only [Function.comp_apply] using hasSum_fintype (fun i : Fin k => f i.succ.val)
  exact (tailLabel_injective.hasSum_iff (f := f) (a := ∑ i : Fin k, f i.succ.val) hoff).mp hf

theorem extendFiniteTailVector_eq_zero_off (a : Fin k → ℝ) (n : ℕ)
    (hn : n ∉ Set.range (fun i : Fin k => i.succ.val)) : extendFiniteTailVector a n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      have hnot : ¬n < k := fun h => hn ⟨⟨n, h⟩, rfl⟩
      simp only [extendFiniteTailVector, extendFiniteVector, dif_neg hnot]

theorem extendFiniteTailVector_hasSum (a : Fin k → ℝ) :
    HasSum (extendFiniteTailVector a) (∑ i, a i) := by
  simpa only [extendFiniteTailVector_succ_val] using
    tail_hasSum (extendFiniteTailVector a) (extendFiniteTailVector_eq_zero_off a)

theorem allocationFeasible_extendFiniteTailVector {u : Fin k → ℝ}
    (hu : u ∈ allocationSimplex (Fin k)) : AllocationFeasible (extendFiniteTailVector u) := by
  have hnonneg : ∀ n, 0 ≤ extendFiniteTailVector u n := by
    intro n
    cases n with
    | zero => exact le_rfl
    | succ n => exact extendFiniteVector_nonneg hu.1 n
  refine ⟨hnonneg, (extendFiniteTailVector_hasSum u).summable, ?_⟩
  rw [(extendFiniteTailVector_hasSum u).tsum_eq]
  exact hu.2

theorem allocationSimplex_restrict_tail {u : ℕ → ℝ} (hu : AllocationFeasible u) :
    (fun i : Fin k => u i.succ.val) ∈ allocationSimplex (Fin k) := by
  refine ⟨fun i => hu.1 _, ?_⟩
  have h := hu.2.1.sum_le_tsum (Finset.univ.image (fun i : Fin k => i.succ.val))
    (fun i _ => hu.1 i)
  rw [Finset.sum_image (fun i _ j _ hij => tailLabel_injective hij)] at h
  exact h.trans hu.2.2

theorem countableAllocationObjective_extendFiniteTailVector
    (a : Fin k → ℝ) (t : ℝ) (u : ℕ → ℝ) :
    countableAllocationObjective (extendFiniteTailVector a) t u =
      ∑ i : Fin k, a i * (u i.succ.val / (u i.succ.val + t ^ 2 * (a i) ^ 2)) ^ (1 / 4 : ℝ) := by
  let f : ℕ → ℝ := fun n => extendFiniteTailVector a n *
    (u n / (u n + t ^ 2 * (extendFiniteTailVector a n) ^ 2)) ^ (1 / 4 : ℝ)
  have hoff : ∀ n, n ∉ Set.range (fun i : Fin k => i.succ.val) → f n = 0 := by
    intro n hn
    simp only [f, extendFiniteTailVector_eq_zero_off a n hn, zero_mul]
  simpa only [countableAllocationObjective, f, extendFiniteTailVector_succ_val] using
    (tail_hasSum f hoff).tsum_eq

theorem allocationD_extendFiniteTailVector_eq_optimizer
    {a u : Fin k → ℝ} {t : ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu : u ∈ allocationSimplex (Fin k))
    (hmax : ∀ v : Fin k → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    allocationD (extendFiniteTailVector a) t = allocationObjective t a u := by
  have hobjective (v : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n) :
      countableAllocationObjective (extendFiniteTailVector a) t v =
        allocationObjective t a (fun i : Fin k => v i.succ.val) := by
    rw [countableAllocationObjective_extendFiniteTailVector]
    exact (allocationObjective_eq_rpow ht ha (fun i => hv i.succ.val)).symm
  have hvalue : countableAllocationObjective (extendFiniteTailVector a) t
      (extendFiniteTailVector u) = allocationObjective t a u := by
    rw [hobjective _ (allocationFeasible_extendFiniteTailVector hu).1]
    simp only [extendFiniteTailVector_succ_val]
  have hmem : allocationObjective t a u ∈ {d : ℝ | ∃ v, AllocationFeasible v ∧
      d = countableAllocationObjective (extendFiniteTailVector a) t v} :=
    ⟨extendFiniteTailVector u, allocationFeasible_extendFiniteTailVector hu, hvalue.symm⟩
  have hbound : ∀ d ∈ {d : ℝ | ∃ v, AllocationFeasible v ∧
      d = countableAllocationObjective (extendFiniteTailVector a) t v}, d ≤ allocationObjective t a u := by
    rintro d ⟨v, hv, rfl⟩
    rw [hobjective v hv.1]
    exact hmax _ (allocationSimplex_restrict_tail hv).1 (allocationSimplex_restrict_tail hv).2
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hbound) (le_csSup ⟨_, hbound⟩ hmem)

theorem largestIndex_extendFiniteLaw_heavy (q : Probability (Fin (k + 1)))
    (hR : tailTotal q ≤ (1 : ℝ) / 4) : largestIndex (extendFiniteLaw q) = 0 := by
  have htotal := reference_head_tail q
  have hhead : (3 : ℝ) / 4 ≤ q.mass 0 := by linarith only [htotal, hR]
  have hmax : ∀ n, (extendFiniteLaw q).mass n ≤ (extendFiniteLaw q).mass 0 := by
    intro n
    rw [show (extendFiniteLaw q).mass 0 = q.mass 0 from extendFiniteLaw_mass_val q 0]
    by_cases hn : n < k + 1
    · rw [show (extendFiniteLaw q).mass n = q.mass ⟨n, hn⟩ from extendFiniteLaw_mass_val q ⟨n, hn⟩]
      have hf : ∀ i : Fin (k + 1), q.mass i ≤ q.mass 0 := by
        intro i
        refine Fin.cases (le_refl _) (fun j => ?_) i
        have hj := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => q.nonneg l.succ)
          (Finset.mem_univ j)
        change q.mass j.succ ≤ tailTotal q at hj
        linarith only [hj, hR, hhead]
      exact hf _
    · rw [extendFiniteLaw_mass_of_not_lt q n hn]
      exact q.nonneg 0
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le hmax)

theorem largestMass_extendFiniteLaw_heavy (q : Probability (Fin (k + 1)))
    (hR : tailTotal q ≤ (1 : ℝ) / 4) : largestMass (extendFiniteLaw q) = q.mass 0 := by
  rw [largestMass_eq_selected, largestIndex_extendFiniteLaw_heavy q hR]
  exact extendFiniteLaw_mass_val q 0

theorem tailMasses_extendFiniteLaw_heavy (q : Probability (Fin (k + 1)))
    (hR : tailTotal q ≤ (1 : ℝ) / 4) :
    tailMasses (extendFiniteLaw q) = extendFiniteTailVector (fun i : Fin k => q.mass i.succ) := by
  funext n
  rw [tailMasses, largestIndex_extendFiniteLaw_heavy q hR]
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, extendFiniteTailVector]
      by_cases hn : n < k
      · rw [show (extendFiniteLaw q).mass (n + 1) = q.mass (⟨n, hn⟩ : Fin k).succ from
          extendFiniteLaw_mass_val q (⟨n, hn⟩ : Fin k).succ]
        exact (extendFiniteVector_val (fun i : Fin k => q.mass i.succ) ⟨n, hn⟩).symm
      · rw [extendFiniteLaw_mass_of_not_lt q (n + 1) (by omega)]
        simp only [extendFiniteVector, dif_neg hn]

theorem exists_finite_heavy_coordinates_at_root
    (q : Probability (Fin (k + 1))) (hq : ∀ i, 0 < q.mass i)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    {ε : ℝ} (hε : 0 < ε) :
    0 < heavyRoot (extendFiniteLaw q) ε ∧
      ∃ x : Fin k → ℝ, (∀ i, 0 < x i ∧ x i < 1) ∧
        (∑ i, q.mass i.succ * x i) +
          Real.sqrt (tailTotal q / heavyRoot (extendFiniteLaw q) ε) = ε ∧
        (heavyRoot (extendFiniteLaw q) ε) ^ 2 *
          (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1 := by
  have hk : 0 < k := by
    by_contra h
    have hk0 := Nat.eq_zero_of_not_pos h
    subst k
    simp only [tailTotal, Finset.univ_eq_empty, Finset.sum_empty] at hR0
    exact (lt_irrefl 0) hR0
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have htotal := reference_head_tail q
  have hlarge : largestMass (extendFiniteLaw q) < 1 := by
    rw [largestMass_extendFiniteLaw_heavy q hR]
    linarith only [htotal, hR0]
  have hroot := heavyRoot_spec (extendFiniteLaw q) hlarge hε
  let T := heavyRoot (extendFiniteLaw q) ε
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer hroot.1 (fun i : Fin k => hq i.succ)
  have hvalue := allocationD_extendFiniteTailVector_eq_optimizer hroot.1
    (fun i : Fin k => hq i.succ) ⟨(fun i => (hu0 i).le), hu1.le⟩ hmax
  have hrootEq := heavyRoot_equation (extendFiniteLaw q) hlarge hε
  rw [tailMasses_extendFiniteLaw_heavy q hR, largestMass_extendFiniteLaw_heavy q hR, hvalue] at hrootEq
  have hRformula : 1 - q.mass 0 = tailTotal q := by linarith only [htotal]
  rw [hRformula] at hrootEq
  let x : Fin k → ℝ := fun i => allocationCoordinate T (q.mass i.succ) (u i)
  refine ⟨hroot.1, x, ?_, hrootEq, ?_⟩
  · intro i
    exact ⟨allocationCoordinate_pos hroot.1 (hq i.succ) (hu0 i),
      (allocationCoordinate_range hroot.1 (hq i.succ) (hu0 i).le).2⟩
  · exact (allocation_constructed_budget_eq Finset.univ T (fun i : Fin k => q.mass i.succ) u
      hroot.1 (fun i _ => hq i.succ) (fun i _ => (hu0 i).le)).symm.trans hu1

end IdentityTesting
