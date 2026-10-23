import IdentityTesting.CollisionTesting

/-! Counting ordered overlapping pairs by an injective triple encoding. -/

noncomputable section
namespace IdentityTesting.CollisionTesting

theorem twoSet_eq_pair_at {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : s.card = 2) {i : α} (hi : i ∈ s) : ∃ j, i ≠ j ∧ s = {i, j} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, Ne.symm hab, Finset.pair_comm _ _⟩

theorem overlapping_twoSets_triple {α : Type*} [DecidableEq α]
    {s t : Finset α} (hs : s.card = 2) (ht : t.card = 2)
    (hinter : (s ∩ t).Nonempty) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ s = {i, j} ∧ t = {i, k} := by
  obtain ⟨i, hi⟩ := hinter
  obtain ⟨his, hit⟩ := Finset.mem_inter.mp hi
  obtain ⟨j, hij, hs⟩ := twoSet_eq_pair_at hs his
  obtain ⟨k, hik, ht⟩ := twoSet_eq_pair_at ht hit
  exact ⟨i, j, k, hij, hik, hs, ht⟩

theorem overlapping_twoSets_union_card {α : Type*} [DecidableEq α]
    {s t : Finset α} (hs : s.card = 2) (ht : t.card = 2)
    (hinter : (s ∩ t).Nonempty) (hne : s ≠ t) : (s ∪ t).card = 3 := by
  obtain ⟨i, j, k, hij, hik, hs, ht⟩ := overlapping_twoSets_triple hs ht hinter
  have hjk : j ≠ k := by
    intro hjk
    apply hne
    rw [hs, ht, hjk]
  have hunion : ({i, j} : Finset α) ∪ {i, k} = {i, j, k} := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ((hi | hj) | (hi | hk))
      · exact Or.inl hi
      · exact Or.inr (Or.inl hj)
      · exact Or.inl hi
      · exact Or.inr (Or.inr hk)
    · rintro (hi | hj | hk)
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr (Or.inr hk)
  rw [hs, ht, hunion]
  simp [hij, hik, hjk]

def orderedOverlapPairs (n : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((collisionPairs n).product (collisionPairs n)).filter (fun st => ¬ Disjoint st.1 st.2)

/-- This even counts equal pairs among the overlaps. -/
theorem orderedOverlapPairs_card_le (n : ℕ) : (orderedOverlapPairs n).card ≤ n ^ 3 := by
  classical
  have hex (st : ↥(orderedOverlapPairs n)) :
      ∃ i j k : Fin n, st.1.1 = {i, j} ∧ st.1.2 = {i, k} := by
    obtain ⟨hp, hdis⟩ := Finset.mem_filter.mp st.2
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hp
    have hinter : (st.1.1 ∩ st.1.2).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hdis
    obtain ⟨i, j, k, _, _, hi, hj⟩ := overlapping_twoSets_triple
      (Finset.mem_powersetCard.mp hs).2 (Finset.mem_powersetCard.mp ht).2 hinter
    exact ⟨i, j, k, hi, hj⟩
  choose i j k hs ht using hex
  let encode : ↥(orderedOverlapPairs n) → Fin n × Fin n × Fin n := fun st => (i st, j st, k st)
  have hinj : Function.Injective encode := by
    intro x y h
    have hi : i x = i y := congrArg Prod.fst h
    have hj : j x = j y := congrArg (fun z : Fin n × Fin n × Fin n => z.2.1) h
    have hk : k x = k y := congrArg (fun z : Fin n × Fin n × Fin n => z.2.2) h
    apply Subtype.ext
    apply Prod.ext
    · rw [hs x, hs y, hi, hj]
    · rw [ht x, ht y, hi, hk]
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa [pow_succ, Nat.mul_assoc] using hcard

end IdentityTesting.CollisionTesting
