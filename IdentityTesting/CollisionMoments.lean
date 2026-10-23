import IdentityTesting.CollisionTesting

/-! Actual pair-product moments used by the collision variance argument. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.CollisionTesting
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def pairCollisionCount (L : Finset Ω) {n : ℕ} (s : Finset (Fin n)) (sample : Fin n → Ω) : ℝ :=
  ∑ x ∈ L, cylinderIndicator s (fun _ => x) sample

omit [Fintype Ω] in
theorem cylinder_constant_mul_same {n : ℕ} (s t : Finset (Fin n)) (x : Ω)
    (sample : Fin n → Ω) :
    cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => x) sample =
      cylinderIndicator (s ∪ t) (fun _ => x) sample := by
  simp only [cylinderIndicator, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

omit [Fintype Ω] in
theorem cylinder_constant_mul_zero_of_overlap {n : ℕ} (s t : Finset (Fin n))
    (hinter : (s ∩ t).Nonempty) {x y : Ω} (hxy : x ≠ y) (sample : Fin n → Ω) :
    cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample = 0 := by
  obtain ⟨j, hj⟩ := hinter
  obtain ⟨hjs, hjt⟩ := Finset.mem_inter.mp hj
  by_cases hs : ∀ i ∈ s, sample i = x
  · have ht : ¬ ∀ i ∈ t, sample i = y := by
      intro ht
      exact hxy ((hs j hjs).symm.trans (ht j hjt))
    simp [cylinderIndicator, ht]
  · simp [cylinderIndicator, hs]

omit [Fintype Ω] in
theorem cylinder_constant_mul_disjoint {n : ℕ} (s t : Finset (Fin n))
    (hdis : Disjoint s t) (x y : Ω) (sample : Fin n → Ω) :
    cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample =
      cylinderIndicator (s ∪ t) (fun i => if i ∈ s then x else y) sample := by
  have hiff : (∀ i ∈ s ∪ t, sample i = if i ∈ s then x else y) ↔
      (∀ i ∈ s, sample i = x) ∧ (∀ i ∈ t, sample i = y) := by
    constructor
    · intro h
      constructor
      · intro i hi
        simpa only [if_pos hi] using h i (Finset.mem_union_left t hi)
      · intro i hi
        have hnot : i ∉ s := fun his => Finset.disjoint_left.mp hdis his hi
        simpa only [if_neg hnot] using h i (Finset.mem_union_right s hi)
    · rintro ⟨hs, ht⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · simpa only [if_pos hi] using hs i hi
      · have hnot : i ∉ s := fun his => Finset.disjoint_left.mp hdis his hi
        simpa only [if_neg hnot] using ht i hi
  change (if ∀ i ∈ s, sample i = x then (1 : ℝ) else 0) *
      (if ∀ i ∈ t, sample i = y then (1 : ℝ) else 0) =
      if ∀ i ∈ s ∪ t, sample i = if i ∈ s then x else y then 1 else 0
  by_cases hs : ∀ i ∈ s, sample i = x
  · by_cases ht : ∀ i ∈ t, sample i = y
    · have hboth := hiff.mpr ⟨hs, ht⟩
      simp only [if_pos hs, if_pos ht, if_pos hboth, mul_one]
    · have hboth : ¬ ∀ i ∈ s ∪ t, sample i = if i ∈ s then x else y :=
        fun h => ht (hiff.mp h).2
      simp only [if_pos hs, if_neg ht, if_neg hboth, mul_zero]
  · have hboth : ¬ ∀ i ∈ s ∪ t, sample i = if i ∈ s then x else y :=
      fun h => hs (hiff.mp h).1
    simp only [if_neg hs, if_neg hboth, zero_mul]

theorem mean_cylinder_constant_mul_disjoint (p : Probability Ω) {n : ℕ}
    (s t : Finset (Fin n)) (hdis : Disjoint s t) (x y : Ω) :
    mean (productLaw p n) (fun sample =>
      cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample) =
      p.mass x ^ s.card * p.mass y ^ t.card := by
  have hfun : (fun sample => cylinderIndicator s (fun _ => x) sample *
      cylinderIndicator t (fun _ => y) sample) =
      cylinderIndicator (s ∪ t) (fun i => if i ∈ s then x else y) :=
    funext (cylinder_constant_mul_disjoint s t hdis x y)
  rw [hfun, mean_productLaw_cylinder, Finset.prod_union hdis]
  congr 1
  · calc
      (∏ j ∈ s, p.mass (if j ∈ s then x else y)) = ∏ _j ∈ s, p.mass x := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_pos hj]
      _ = p.mass x ^ s.card := by simp
  · calc
      (∏ j ∈ t, p.mass (if j ∈ s then x else y)) = ∏ _j ∈ t, p.mass y := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_neg (fun hjs => Finset.disjoint_left.mp hdis hjs hj)]
      _ = p.mass y ^ t.card := by simp

theorem mean_pairCollisionCount_mul_overlap (p : Probability Ω) (L : Finset Ω) {n : ℕ}
    (s t : Finset (Fin n)) (hinter : (s ∩ t).Nonempty) :
    mean (productLaw p n) (fun sample => pairCollisionCount L s sample * pairCollisionCount L t sample) =
      ∑ x ∈ L, p.mass x ^ (s ∪ t).card := by
  classical
  have hfun : (fun sample => pairCollisionCount L s sample * pairCollisionCount L t sample) =
      (fun sample => ∑ x ∈ L, ∑ y ∈ L,
        cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample) := by
    funext sample
    simp only [pairCollisionCount, Finset.sum_mul_sum]
  rw [hfun, mean_finset_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mean_finset_sum]
  calc
    (∑ y ∈ L, mean (productLaw p n) (fun sample =>
        cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample)) =
        mean (productLaw p n) (cylinderIndicator (s ∪ t) (fun _ => x)) := by
      rw [Finset.sum_eq_single x]
      · congr 1
        funext sample
        exact cylinder_constant_mul_same s t x sample
      · intro y _ hy
        have hzero : (fun sample => cylinderIndicator s (fun _ => x) sample *
            cylinderIndicator t (fun _ => y) sample) = fun _ => (0 : ℝ) :=
          funext (cylinder_constant_mul_zero_of_overlap s t hinter (Ne.symm hy))
        rw [hzero]
        simp [mean]
      · exact fun h => (h hx).elim
    _ = p.mass x ^ (s ∪ t).card := mean_productLaw_constant_cylinder p n (s ∪ t) x

theorem mean_pairCollisionCount_mul_disjoint (p : Probability Ω) (L : Finset Ω) {n : ℕ}
    (s t : Finset (Fin n)) (hdis : Disjoint s t) (hs : s.card = 2) (ht : t.card = 2) :
    mean (productLaw p n) (fun sample => pairCollisionCount L s sample * pairCollisionCount L t sample) =
      collisionMass2 p L ^ 2 := by
  have hfun : (fun sample => pairCollisionCount L s sample * pairCollisionCount L t sample) =
      (fun sample => ∑ x ∈ L, ∑ y ∈ L,
        cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample) := by
    funext sample
    simp only [pairCollisionCount, Finset.sum_mul_sum]
  rw [hfun, mean_finset_sum]
  calc
    (∑ x ∈ L, mean (productLaw p n) (fun sample => ∑ y ∈ L,
        cylinderIndicator s (fun _ => x) sample * cylinderIndicator t (fun _ => y) sample)) =
        ∑ x ∈ L, ∑ y ∈ L, p.mass x ^ 2 * p.mass y ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [mean_finset_sum]
      apply Finset.sum_congr rfl
      intro y _
      simpa only [hs, ht] using mean_cylinder_constant_mul_disjoint p s t hdis x y
    _ = collisionMass2 p L ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, collisionMass2, pow_two]

end IdentityTesting.CollisionTesting
