import IdentityTesting.CountableOverlap
import IdentityTesting.FiniteTesting

/-! Retaining a finite set of labels and pooling its complement as one label.
The resulting finite law is normalized and is the actual pushforward of the
original law.  Transfer of an arbitrary n-sample test is a further obligation. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

abbrev PoolLabel (s : Finset ℕ) := Option {i : ℕ // i ∈ s}

def poolMap (s : Finset ℕ) (i : ℕ) : PoolLabel s :=
  if h : i ∈ s then some ⟨i, h⟩ else none

def pooledLaw (p : DiscreteLaw) (s : Finset ℕ) : FiniteTesting.Probability (PoolLabel s) where
  mass x := match x with
    | none => residualMass p s
    | some i => p.mass i
  nonneg x := by
    cases x with
    | none => exact tsum_nonneg (fun i => p.nonneg i)
    | some i => exact p.nonneg i
  total := by
    rw [Fintype.sum_option]
    change residualMass p s + (∑ i : s, p.mass i) = 1
    rw [← Finset.sum_subtype s (fun _ => Iff.rfl) p.mass, add_comm]
    exact p.summable.sum_add_tsum_compl.trans p.total

@[simp] theorem poolMap_eq_none (s : Finset ℕ) (i : ℕ) :
    poolMap s i = none ↔ i ∉ s := by
  simp [poolMap]

@[simp] theorem poolMap_eq_some (s : Finset ℕ) (i : ℕ) (j : s) :
    poolMap s i = some j ↔ i = j.val := by
  by_cases hi : i ∈ s
  · simp [poolMap, hi, Subtype.ext_iff]
  · simp only [poolMap, dif_neg hi, reduceCtorEq, false_iff]
    intro h
    exact hi (h ▸ j.property)

/-- Each pooled atom is exactly the mass of its preimage under the label map. -/
theorem pooledLaw_mass_fiber (p : DiscreteLaw) (s : Finset ℕ) (x : PoolLabel s) :
    (pooledLaw p s).mass x = ∑' i : {i : ℕ // poolMap s i = x}, p.mass i := by
  cases x with
  | none =>
      let e : {i : ℕ // poolMap s i = none} ≃ {i : ℕ // i ∉ s} :=
        { toFun := fun i => ⟨i.val, (poolMap_eq_none s i.val).mp i.property⟩
          invFun := fun i => ⟨i.val, (poolMap_eq_none s i.val).mpr i.property⟩
          left_inv := fun i => Subtype.ext rfl
          right_inv := fun i => Subtype.ext rfl }
      exact (e.tsum_eq (fun i => p.mass i)).symm
  | some j =>
      let k : {i : ℕ // poolMap s i = some j} :=
        ⟨j.val, (poolMap_eq_some s j.val j).mpr rfl⟩
      have hall : ∀ i : {i : ℕ // poolMap s i = some j}, i = k := by
        intro i
        exact Subtype.ext ((poolMap_eq_some s i.val j).mp i.property)
      have hsum : (∑' i : {i : ℕ // poolMap s i = some j}, p.mass i) = p.mass k :=
        tsum_eq_single k (fun i hi => False.elim (hi (hall i)))
      exact hsum.symm

theorem finite_totalVariation_eq_one_sub_overlap {Ω : Type*} [Fintype Ω]
    (p q : FiniteTesting.Probability Ω) :
    FiniteTesting.totalVariation p q = 1 - ∑ i, min (p.mass i) (q.mass i) := by
  unfold FiniteTesting.totalVariation
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, p.total, q.total]
  ring

/-- The previously derived pooling formula is the TV of the constructed laws. -/
theorem pooledLaw_totalVariation (p q : DiscreteLaw) (s : Finset ℕ) :
    FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) =
      pooledTVFormula p q s := by
  rw [finite_totalVariation_eq_one_sub_overlap, Fintype.sum_option]
  change 1 - (min (residualMass p s) (residualMass q s) +
    ∑ i : s, min (p.mass i) (q.mass i)) = pooledTVFormula p q s
  rw [← Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => min (p.mass i) (q.mass i))]
  unfold pooledTVFormula
  ring

theorem strict_alternative_survives_pooling (p q : DiscreteLaw) (s : Finset ℕ)
    (ε : ℝ) (h : ε < totalVariation p q) :
    ε - residualMass q s <
      FiniteTesting.totalVariation (pooledLaw p s) (pooledLaw q s) := by
  rw [pooledLaw_totalVariation]
  exact strict_alternative_survives_pooling_formula p q s ε h

end IdentityTesting
