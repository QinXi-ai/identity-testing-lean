import IdentityTesting.FiniteIID
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt

/-!
# Collision tests on actual finite IID samples

Unordered sample pairs are represented by two-element subsets.  The collision
count and the deterministic repeat test are defined on the actual sample tuple.
Their expectation and null repeat bound are derived from IID cylinder masses.
The actual variance bound and numerical alternative no-repeat bound are
assembled in the dependent modules `CollisionVariance` and `CollisionDetection`.
-/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.CollisionTesting
open FiniteTesting FiniteIID

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def collisionPairs (n : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard 2

def collisionMass2 (p : Probability Ω) (L : Finset Ω) : ℝ := ∑ x ∈ L, p.mass x ^ 2

def collisionCount (L : Finset Ω) (n : ℕ) (sample : Fin n → Ω) : ℝ :=
  ∑ s ∈ collisionPairs n, ∑ x ∈ L, cylinderIndicator s (fun _ => x) sample

def HasRepeat (L : Finset Ω) {n : ℕ} (sample : Fin n → Ω) : Prop :=
  ∃ i j, i ≠ j ∧ sample i = sample j ∧ sample i ∈ L

def repeatTest (L : Finset Ω) (n : ℕ) : RandomizedTest (Fin n → Ω) := by
  classical
  exact {
    reject := fun sample => if HasRepeat L sample then 1 else 0
    nonneg := fun sample => by split <;> norm_num
    le_one := fun sample => by split <;> norm_num }

omit [Fintype Ω] in
theorem collisionCount_nonneg (L : Finset Ω) (n : ℕ) (sample : Fin n → Ω) :
    0 ≤ collisionCount L n sample := by
  apply Finset.sum_nonneg
  intro s _
  exact Finset.sum_nonneg (fun x _ => cylinderIndicator_nonneg s (fun _ => x) sample)

/-- Exact first moment of the actual unordered collision count. -/
theorem mean_collisionCount (p : Probability Ω) (L : Finset Ω) (n : ℕ) :
    mean (productLaw p n) (collisionCount L n) = (n.choose 2 : ℝ) * collisionMass2 p L := by
  unfold collisionCount
  rw [mean_finset_sum]
  calc
    (∑ s ∈ collisionPairs n,
        mean (productLaw p n) (fun sample => ∑ x ∈ L, cylinderIndicator s (fun _ => x) sample)) =
        ∑ s ∈ collisionPairs n, collisionMass2 p L := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [mean_finset_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [mean_productLaw_constant_cylinder]
      rw [(Finset.mem_powersetCard.mp hs).2]
    _ = (n.choose 2 : ℝ) * collisionMass2 p L := by
      simp [collisionPairs]

omit [Fintype Ω] in
theorem repeatTest_le_collisionCount (L : Finset Ω) (n : ℕ) (sample : Fin n → Ω) :
    (repeatTest L n).reject sample ≤ collisionCount L n sample := by
  by_cases h : HasRepeat L sample
  · obtain ⟨i, j, hij, heq, hL⟩ := h
    have hpair : ({i, j} : Finset (Fin n)) ∈ collisionPairs n := by
      simp [collisionPairs, Finset.card_pair hij]
    have hcyl : cylinderIndicator {i, j} (fun _ => sample i) sample = 1 := by
      simp [cylinderIndicator, heq]
    have hlabel : 1 ≤ ∑ x ∈ L, cylinderIndicator {i, j} (fun _ => x) sample := by
      rw [← hcyl]
      exact Finset.single_le_sum (fun x _ => cylinderIndicator_nonneg {i, j} (fun _ => x) sample) hL
    have hsum : (∑ x ∈ L, cylinderIndicator {i, j} (fun _ => x) sample) ≤
        collisionCount L n sample := by
      exact Finset.single_le_sum
        (fun s _ => Finset.sum_nonneg (fun x _ => cylinderIndicator_nonneg s (fun _ => x) sample)) hpair
    have hrepeat : HasRepeat L sample := ⟨i, j, hij, heq, hL⟩
    simpa only [repeatTest, if_pos hrepeat] using hlabel.trans hsum
  · simpa only [repeatTest, if_neg h] using collisionCount_nonneg L n sample

/-- Null repeat union bound, with no supplied moment or probability hypothesis.
This also covers sample sizes zero and one. -/
theorem repeat_probability_le (p : Probability Ω) (L : Finset Ω) (n : ℕ) :
    expectation (productLaw p n) (repeatTest L n) ≤
      (n.choose 2 : ℝ) * (∑ x ∈ L, p.mass x ^ 2) := by
  change mean (productLaw p n) (repeatTest L n).reject ≤ _
  calc
    mean (productLaw p n) (repeatTest L n).reject ≤
        mean (productLaw p n) (collisionCount L n) :=
      mean_mono _ (repeatTest_le_collisionCount L n)
    _ = (n.choose 2 : ℝ) * (∑ x ∈ L, p.mass x ^ 2) := mean_collisionCount p L n

omit [Fintype Ω] in
theorem collisionCount_eq_zero_of_no_repeat (L : Finset Ω) (n : ℕ)
    (sample : Fin n → Ω) (h : ¬ HasRepeat L sample) : collisionCount L n sample = 0 := by
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro x hx
  unfold cylinderIndicator
  apply if_neg
  intro hc
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
  have hi : sample i = x := hc i (by simp)
  have hj : sample j = x := hc j (by simp)
  exact h ⟨i, j, hij, hi.trans hj.symm, by simpa only [hi] using hx⟩

def collisionVariance (p : Probability Ω) (L : Finset Ω) (n : ℕ) : ℝ :=
  mean (productLaw p n) (fun sample =>
    (collisionCount L n sample - mean (productLaw p n) (collisionCount L n)) ^ 2)

/-- Chebyshev's zero-event argument for the actual collision statistic.
The variance is an explicitly defined expectation, not a supplied bound.
`CollisionVariance` supplies its upper bound, and `CollisionDetection` derives
the manuscript's numerical alternative bound. -/
theorem no_repeat_probability_le_variance (p : Probability Ω) (L : Finset Ω) (n : ℕ)
    (hn : 2 ≤ n) (hp2 : 0 < collisionMass2 p L) :
    1 - expectation (productLaw p n) (repeatTest L n) ≤
      collisionVariance p L n / ((n.choose 2 : ℝ) * collisionMass2 p L) ^ 2 := by
  let c := mean (productLaw p n) (collisionCount L n)
  have hc : 0 < c := by
    dsimp [c]
    rw [mean_collisionCount]
    exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hn)) hp2
  have hpoint (sample : Fin n → Ω) :
      c ^ 2 * (1 - (repeatTest L n).reject sample) ≤ (collisionCount L n sample - c) ^ 2 := by
    by_cases h : HasRepeat L sample
    · simpa only [repeatTest, if_pos h, sub_self, mul_zero] using
        sq_nonneg (collisionCount L n sample - c)
    · rw [collisionCount_eq_zero_of_no_repeat L n sample h]
      simp [repeatTest, h]
  have hmean := mean_mono (productLaw p n) hpoint
  have hleft : mean (productLaw p n) (fun sample => c ^ 2 * (1 - (repeatTest L n).reject sample)) =
      c ^ 2 * (1 - expectation (productLaw p n) (repeatTest L n)) := by
    unfold mean expectation
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [← Finset.sum_mul, (productLaw p n).total, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro sample _
    ring
  rw [hleft] at hmean
  have hbound : 1 - expectation (productLaw p n) (repeatTest L n) ≤ collisionVariance p L n / c ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hc)).2
    simpa only [mul_comm, collisionVariance, c] using hmean
  simpa only [c, mean_collisionCount] using hbound

def collisionMass3 (p : Probability Ω) (L : Finset Ω) : ℝ := ∑ x ∈ L, p.mass x ^ 3

omit [DecidableEq Ω] in
theorem collisionMass3_le_mass2_sqrt (p : Probability Ω) (L : Finset Ω) :
    collisionMass3 p L ≤ collisionMass2 p L * Real.sqrt (collisionMass2 p L) := by
  calc
    collisionMass3 p L ≤ ∑ x ∈ L, p.mass x ^ 2 * Real.sqrt (collisionMass2 p L) := by
      apply Finset.sum_le_sum
      intro x hx
      have hs : p.mass x ^ 2 ≤ collisionMass2 p L :=
        Finset.single_le_sum (fun y _ => sq_nonneg (p.mass y)) hx
      have hxle : p.mass x ≤ Real.sqrt (collisionMass2 p L) := Real.le_sqrt_of_sq_le hs
      calc
        p.mass x ^ 3 = p.mass x ^ 2 * p.mass x := by ring
        _ ≤ p.mass x ^ 2 * Real.sqrt (collisionMass2 p L) :=
          mul_le_mul_of_nonneg_left hxle (sq_nonneg _)
    _ = collisionMass2 p L * Real.sqrt (collisionMass2 p L) := by
      rw [← Finset.sum_mul]
      rfl

end IdentityTesting.CollisionTesting
