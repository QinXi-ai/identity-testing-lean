import IdentityTesting.CountableEmbedding
import IdentityTesting.FiniteAllocationEmbedding
import IdentityTesting.GeneralAllocationLowerBound

/-! Remove zero masses and label-order restrictions without changing the experiment. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators
open Classical FiniteTesting

private theorem law_ext {p q : DiscreteLaw} (h : ∀ n, p.mass n = q.mass n) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

theorem exists_injective_extension {k : ℕ} (e : Fin k → ℕ) (he : Function.Injective e) :
    ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ i : Fin k, f i.val = e i := by
  let M : ℕ := (∑ i, e i) + 1
  have hM : ∀ i, e i < M := by
    intro i
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (e j))
      (Finset.mem_univ i)
    dsimp only [M]
    omega
  let f : ℕ → ℕ := fun n => if h : n < k then e ⟨n, h⟩ else M + n
  have hval : ∀ i : Fin k, f i.val = e i := by intro i; simp only [f, dif_pos i.isLt]
  refine ⟨f, ?_, hval⟩
  intro a b hab
  by_cases ha : a < k <;> by_cases hb : b < k
  · have h : e ⟨a, ha⟩ = e ⟨b, hb⟩ := by simpa only [f, dif_pos ha, dif_pos hb] using hab
    exact congrArg Fin.val (he h)
  · have h := hM ⟨a, ha⟩
    simp only [f, dif_pos ha, dif_neg hb] at hab
    omega
  · have h := hM ⟨b, hb⟩
    simp only [f, dif_neg ha, dif_pos hb] at hab
    omega
  · simpa only [f, dif_neg ha, dif_neg hb, Nat.add_left_cancel_iff] using hab

theorem injectLaw_extendFiniteLaw_eq {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k))
    (e : Fin k → ℕ) (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (f : ℕ → ℕ) (hf : Function.Injective f) (hfe : ∀ i : Fin k, f i.val = e i) :
    injectLaw f hf (extendFiniteLaw p) = q := by
  have hm : ∀ n, (injectLaw f hf (extendFiniteLaw p)).mass n = q.mass n := by
    intro n
    by_cases hn : n ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hn
      change injectMass f (extendFiniteLaw p) (f j) = q.mass (f j)
      rw [injectMass_apply f hf]
      by_cases hj : j < k
      · rw [hfe ⟨j, hj⟩, hmass]
        exact extendFiniteLaw_mass_val p ⟨j, hj⟩
      · rw [extendFiniteLaw_mass_of_not_lt p j hj, hoff]
        rintro ⟨i, hi⟩
        rw [← hfe i] at hi
        have h := hf hi
        exact hj (h ▸ i.isLt)
    · change injectMass f (extendFiniteLaw p) n = q.mass n
      rw [injectMass_off f _ n hn, hoff]
      rintro ⟨i, hi⟩
      exact hn ⟨i.val, (hfe i).trans hi⟩
  exact law_ext hm

theorem hasIdentityTest_of_finite_embedding {k : ℕ}
    (q : DiscreteLaw) (p : Probability (Fin k))
    (e : Fin k → ℕ) (he : Function.Injective e)
    (hmass : ∀ i, q.mass (e i) = p.mass i)
    (hoff : ∀ n, n ∉ Set.range e → q.mass n = 0)
    (ε : ℝ) (n : ℕ) : HasIdentityTest q ε n → HasIdentityTest (extendFiniteLaw p) ε n := by
  obtain ⟨f, hf, hfe⟩ := exists_injective_extension e he
  rw [← injectLaw_extendFiniteLaw_eq q p e hmass hoff f hf hfe]
  exact hasIdentityTest_of_injectLaw f hf (extendFiniteLaw p) ε n

theorem positiveFiniteLaw_countable_embedding {l : ℕ} (q : Probability (Fin l)) :
    let p := positiveFiniteLaw q
    let e := fun i => (positiveEnumeration q i).val
    (∀ i, (extendFiniteLaw q).mass (e i) = p.mass i) ∧
    (∀ n, n ∉ Set.range e → (extendFiniteLaw q).mass n = 0) := by
  dsimp only
  constructor
  · intro i
    rw [extendFiniteLaw_mass_val, positiveFiniteLaw_mass]
  · intro n hn
    by_cases hnlt : n < l
    · rw [show n = (⟨n, hnlt⟩ : Fin l).val from rfl, extendFiniteLaw_mass_val]
      apply le_antisymm _ (q.nonneg _)
      apply le_of_not_gt
      intro hp
      apply hn
      refine ⟨(Fintype.equivFin (PositiveLabel q)) ⟨⟨n, hnlt⟩, hp⟩, ?_⟩
      simp only [positiveEnumeration, Equiv.symm_apply_apply]
    · exact extendFiniteLaw_mass_of_not_lt q n hnlt

theorem allocationRoot_positiveFiniteLaw {l : ℕ} (q : Probability (Fin l)) (ε : ℝ) :
    allocationRoot (extendFiniteLaw q) ε = allocationRoot (extendFiniteLaw (positiveFiniteLaw q)) ε := by
  obtain ⟨hm, hz⟩ := positiveFiniteLaw_countable_embedding q
  exact allocationRoot_of_finite_embedding (extendFiniteLaw q) (positiveFiniteLaw q)
    (positiveFiniteLaw_pos q) (fun i => (positiveEnumeration q i).val)
    (Fin.val_injective.comp (positiveEnumeration_injective q)) hm hz ε

theorem no_identityTest_of_general_allocation_root_with_zeros {l : ℕ}
    (q : Probability (Fin l)) (hcap : ∀ i, q.mass i ≤ (4 : ℝ) / 5)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * allocationRoot (extendFiniteLaw q) ε) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  obtain ⟨hm, hz⟩ := positiveFiniteLaw_countable_embedding q
  have hno := GeneralLowerGeometry.no_identityTest_of_general_allocation_root
    (positiveFiniteLaw q) (positiveFiniteLaw_pos q)
    (fun i => by rw [positiveFiniteLaw_mass]; exact hcap _) ε hε0 hε1 n
    (by rwa [← allocationRoot_positiveFiniteLaw])
  exact fun ht => hno (hasIdentityTest_of_finite_embedding (extendFiniteLaw q)
    (positiveFiniteLaw q) (fun i => (positiveEnumeration q i).val)
    (Fin.val_injective.comp (positiveEnumeration_injective q)) hm hz ε n ht)

end IdentityTesting
