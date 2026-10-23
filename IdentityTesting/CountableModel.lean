import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Countable discrete laws and the original strict-radius testing model. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

structure DiscreteLaw where
  mass : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  summable : Summable mass
  total : ∑' i, mass i = 1

def totalVariation (p q : DiscreteLaw) : ℝ :=
  (∑' i, |p.mass i - q.mass i|) / 2

theorem DiscreteLaw.summable_abs_sub (p q : DiscreteLaw) :
    Summable (fun i => |p.mass i - q.mass i|) :=
  (p.summable.sub q.summable).abs

theorem totalVariation_nonneg (p q : DiscreteLaw) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (tsum_nonneg (fun i => abs_nonneg _)) (by norm_num)

theorem totalVariation_le_one (p q : DiscreteLaw) : totalVariation p q ≤ 1 := by
  have h := Summable.tsum_le_tsum
    (fun i => show |p.mass i - q.mass i| ≤ p.mass i + q.mass i by
      rw [abs_le]
      constructor <;> linarith [p.nonneg i, q.nonneg i])
    (p.summable_abs_sub q) (p.summable.add q.summable)
  rw [tsum_add p.summable q.summable, p.total, q.total] at h
  unfold totalVariation
  linarith

def Sample (n : ℕ) := Fin n → ℕ

def sampleMass (p : DiscreteLaw) (n : ℕ) (x : Sample n) : ℝ :=
  ∏ i, p.mass (x i)

structure RandomizedTest (n : ℕ) where
  reject : Sample n → ℝ
  nonneg : ∀ x, 0 ≤ reject x
  le_one : ∀ x, reject x ≤ 1

def rejectionProbability (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) : ℝ :=
  ∑' x : Sample n, sampleMass p n x * test.reject x

def acceptanceProbability (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) : ℝ :=
  ∑' x : Sample n, sampleMass p n x * (1 - test.reject x)

def IsIdentityTest (q : DiscreteLaw) (ε : ℝ) {n : ℕ} (test : RandomizedTest n) : Prop :=
  rejectionProbability q test ≤ 1 / 3 ∧
  ∀ p : DiscreteLaw, ε < totalVariation p q → acceptanceProbability p test ≤ 1 / 3

def HasIdentityTest (q : DiscreteLaw) (ε : ℝ) (n : ℕ) : Prop :=
  ∃ test : RandomizedTest n, IsIdentityTest q ε test

def acceptAlways (n : ℕ) : RandomizedTest n where
  reject := fun _ => 0
  nonneg := fun _ => le_rfl
  le_one := fun _ => zero_le_one

theorem radius_one_zero_samples (q : DiscreteLaw) : HasIdentityTest q 1 0 := by
  refine ⟨acceptAlways 0, ?_, ?_⟩
  · simp [rejectionProbability, acceptAlways]
  · intro p h
    exact False.elim ((not_lt_of_ge (totalVariation_le_one p q)) h)

end IdentityTesting
