import IdentityTesting.CollisionMoments
import IdentityTesting.CollisionPairCounting

/-! The variance bound for the actual finite IID collision statistic. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.CollisionTesting
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem collisionMass3_nonneg (p : Probability Ω) (L : Finset Ω) :
    0 ≤ collisionMass3 p L :=
  Finset.sum_nonneg (fun x _ => pow_nonneg (p.nonneg x) 3)

theorem mean_pairCollisionCount_mul_le (p : Probability Ω) (L : Finset Ω) {n : ℕ}
    (s t : Finset (Fin n)) (hs : s ∈ collisionPairs n) (ht : t ∈ collisionPairs n) :
    mean (productLaw p n) (fun sample => pairCollisionCount L s sample * pairCollisionCount L t sample) ≤
      (if s = t then collisionMass2 p L else 0) + collisionMass2 p L ^ 2 +
        (if ¬ Disjoint s t then collisionMass3 p L else 0) := by
  classical
  have hs2 := (Finset.mem_powersetCard.mp hs).2
  have ht2 := (Finset.mem_powersetCard.mp ht).2
  by_cases heq : s = t
  · subst t
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hinter : (s ∩ s).Nonempty := by simpa using hsne
    have hnot := Finset.not_disjoint_iff_nonempty_inter.mpr hinter
    have hm := mean_pairCollisionCount_mul_overlap p L s s hinter
    simp only [Finset.union_self, hs2] at hm
    change _ = collisionMass2 p L at hm
    rw [hm]
    simp only [ite_true, if_pos hnot]
    linarith [sq_nonneg (collisionMass2 p L), collisionMass3_nonneg p L]
  · by_cases hdis : Disjoint s t
    · rw [mean_pairCollisionCount_mul_disjoint p L s t hdis hs2 ht2]
      simp [heq, hdis]
    · have hinter := Finset.not_disjoint_iff_nonempty_inter.mp hdis
      have hcard := overlapping_twoSets_union_card hs2 ht2 hinter heq
      have hm := mean_pairCollisionCount_mul_overlap p L s t hinter
      rw [hcard] at hm
      change _ = collisionMass3 p L at hm
      rw [hm]
      simp only [if_neg heq, if_pos hdis, zero_add]
      exact le_add_of_nonneg_left (sq_nonneg _)

theorem mean_collisionCount_sq_le (p : Probability Ω) (L : Finset Ω) (n : ℕ) :
    mean (productLaw p n) (fun sample => collisionCount L n sample ^ 2) ≤
      (n.choose 2 : ℝ) * collisionMass2 p L +
        (n.choose 2 : ℝ) ^ 2 * collisionMass2 p L ^ 2 + (n : ℝ) ^ 3 * collisionMass3 p L := by
  classical
  have hfun : (fun sample => collisionCount L n sample ^ 2) =
      (fun sample => ∑ s ∈ collisionPairs n, ∑ t ∈ collisionPairs n,
        pairCollisionCount L s sample * pairCollisionCount L t sample) := by
    funext sample
    simp only [collisionCount, pairCollisionCount, pow_two, Finset.sum_mul_sum]
  rw [hfun, mean_finset_sum]
  simp_rw [mean_finset_sum]
  have hsum := Finset.sum_le_sum (s := collisionPairs n) (fun s hs =>
    Finset.sum_le_sum (s := collisionPairs n) (fun t ht => mean_pairCollisionCount_mul_le p L s t hs ht))
  have hdiag : (∑ s ∈ collisionPairs n, ∑ t ∈ collisionPairs n,
      if s = t then collisionMass2 p L else 0) = (n.choose 2 : ℝ) * collisionMass2 p L := by
    calc
      _ = ∑ _s ∈ collisionPairs n, collisionMass2 p L := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [hs]
      _ = _ := by simp [collisionPairs]
  have hconst : (∑ _s ∈ collisionPairs n, ∑ _t ∈ collisionPairs n,
      collisionMass2 p L ^ 2) = (n.choose 2 : ℝ) ^ 2 * collisionMass2 p L ^ 2 := by
    simp [collisionPairs, pow_two, mul_assoc]
  have hover : (∑ s ∈ collisionPairs n, ∑ t ∈ collisionPairs n,
      if ¬ Disjoint s t then collisionMass3 p L else 0) =
      ((orderedOverlapPairs n).card : ℝ) * collisionMass3 p L := by
    rw [← Finset.sum_product (collisionPairs n) (collisionPairs n)
      (fun st => if ¬ Disjoint st.1 st.2 then collisionMass3 p L else 0)]
    rw [← Finset.sum_filter
      (fun st : Finset (Fin n) × Finset (Fin n) => ¬ Disjoint st.1 st.2)
      (fun _ => collisionMass3 p L)]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rfl
  simp only [Finset.sum_add_distrib] at hsum
  rw [hdiag, hconst, hover] at hsum
  have hcard : ((orderedOverlapPairs n).card : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      _ ≤ ((n ^ 3 : ℕ) : ℝ) := Nat.cast_le.mpr (orderedOverlapPairs_card_le n)
      _ = _ := by rw [Nat.cast_pow]
  exact hsum.trans (add_le_add_left
    (mul_le_mul_of_nonneg_right hcard (collisionMass3_nonneg p L)) _)

theorem collisionVariance_eq_secondMoment_sub (p : Probability Ω) (L : Finset Ω) (n : ℕ) :
    collisionVariance p L n =
      mean (productLaw p n) (fun sample => collisionCount L n sample ^ 2) -
        mean (productLaw p n) (collisionCount L n) ^ 2 := by
  let c := mean (productLaw p n) (collisionCount L n)
  change mean (productLaw p n) (fun sample => (collisionCount L n sample - c) ^ 2) =
    mean (productLaw p n) (fun sample => collisionCount L n sample ^ 2) - c ^ 2
  unfold mean
  calc
    _ = ∑ sample, ((productLaw p n).mass sample * collisionCount L n sample ^ 2 -
        2 * c * ((productLaw p n).mass sample * collisionCount L n sample) +
          c ^ 2 * (productLaw p n).mass sample) := by
      apply Finset.sum_congr rfl
      intro sample _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        (productLaw p n).total, mul_one]
      change _ - 2 * c * c + c ^ 2 = _ - c ^ 2
      ring

/-- No variance assumption is supplied: the bound follows from the actual IID
pair-product moments and an injective count of overlapping sample pairs. -/
theorem collisionVariance_le (p : Probability Ω) (L : Finset Ω) (n : ℕ) :
    collisionVariance p L n ≤ (n.choose 2 : ℝ) * collisionMass2 p L +
      (n : ℝ) ^ 3 * collisionMass3 p L := by
  rw [collisionVariance_eq_secondMoment_sub, mean_collisionCount]
  have h := mean_collisionCount_sq_le p L n
  nlinarith only [h]

end IdentityTesting.CollisionTesting
