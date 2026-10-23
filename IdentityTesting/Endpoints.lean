import IdentityTesting.CountableOverlap
import IdentityTesting.Sampling

noncomputable section
open scoped BigOperators
open Filter
namespace IdentityTesting

theorem DiscreteLaw.mass_le_one (q : DiscreteLaw) (i : ℕ) : q.mass i ≤ 1 := by
  simpa only [q.total] using q.summable.le_tsum i (fun j _ => q.nonneg j)

def pointMass (j : ℕ) : DiscreteLaw where
  mass i := if i = j then 1 else 0
  nonneg i := by split <;> norm_num
  summable := (hasSum_ite_eq j (1 : ℝ)).summable
  total := (hasSum_ite_eq j (1 : ℝ)).tsum_eq

theorem totalVariation_pointMass (q : DiscreteLaw) (j : ℕ) :
    totalVariation (pointMass j) q = 1 - q.mass j := by
  rw [totalVariation_eq_one_sub_overlap]
  have h : (fun i => min ((pointMass j).mass i) (q.mass i)) =
      (fun i => if i = j then q.mass j else 0) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [pointMass, min_eq_right (q.mass_le_one j)]
    · simp [pointMass, hi, min_eq_left (q.nonneg i)]
  rw [h, tsum_ite_eq]

theorem exists_strict_alternative (q : DiscreteLaw) (ε : ℝ) (hε : ε < 1) :
    ∃ p : DiscreteLaw, ε < totalVariation p q := by
  have hδ : (0 : ℝ) < 1 - ε := by linarith
  have hsmall : ∀ᶠ i in atTop, q.mass i < 1 - ε :=
    q.summable.tendsto_atTop_zero.eventually (gt_mem_nhds hδ)
  obtain ⟨i, hi⟩ := hsmall.exists
  refine ⟨pointMass i, ?_⟩
  rw [totalVariation_pointMass]
  linarith

theorem no_zero_sample_test (q : DiscreteLaw) (ε : ℝ) (hε : ε < 1) :
    ¬ HasIdentityTest q ε 0 := by
  rintro ⟨test, hnull, halt⟩
  obtain ⟨p, hp⟩ := exists_strict_alternative q ε hε
  have ha := halt p hp
  have hr : rejectionProbability p test = rejectionProbability q test := by
    simp [rejectionProbability, sampleMass]
  have htotal := rejection_add_acceptance p test
  linarith

theorem successful_test_uses_positive_samples (q : DiscreteLaw) (ε : ℝ)
    (hε : ε < 1) (n : ℕ) (h : HasIdentityTest q ε n) : 1 ≤ n := by
  cases n with
  | zero => exact False.elim (no_zero_sample_test q ε hε h)
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

end IdentityTesting
