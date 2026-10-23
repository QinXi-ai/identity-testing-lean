import IdentityTesting.CountableModel

/-! The original mathematical target, recorded as a proposition, not a proof. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

def AllocationFeasible (u : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ u i) ∧ Summable u ∧ (∑' i, u i) ≤ 1

def countableAllocationObjective (a : ℕ → ℝ) (t : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑' i, a i * (u i / (u i + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ)

def allocationD (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ u, AllocationFeasible u ∧ v = countableAllocationObjective a t u}

def overlapMoment (q : DiscreteLaw) (δ : ℝ) : ℝ :=
  ∑' i, min (q.mass i) (q.mass i ^ (3 / 2 : ℝ) / Real.sqrt δ)

def largestMass (q : DiscreteLaw) : ℝ := sSup (Set.range q.mass)

def largestIndex (q : DiscreteLaw) : ℕ :=
  sInf {i : ℕ | ∀ j, q.mass j ≤ q.mass i}

def tailMasses (q : DiscreteLaw) (i : ℕ) : ℝ :=
  if i = largestIndex q then 0 else q.mass i

def allocationRoot (q : DiscreteLaw) (e : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ allocationD q.mass t ≤ e}

def heavyRoot (q : DiscreteLaw) (e : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧
    allocationD (tailMasses q) t + Real.sqrt ((1 - largestMass q) / t) ≤ e}

def complexityScale (q : DiscreteLaw) (ε : ℝ) : ℝ :=
  let h := largestMass q
  let R := 1 - h
  let δ := 1 - ε
  if ε = 1 then 0
  else if h = 1 then 1 / ε
  else if 3 / 4 < h then
    if ε ≤ R then heavyRoot q ε
    else min (heavyRoot q R) (R / (ε - R) ^ 2 + 1 / (ε - R))
  else if h / 2 ≤ δ then allocationRoot q ε
  else 1 / overlapMoment q δ

def roundedScale (q : DiscreteLaw) (ε : ℝ) : ℕ := ⌈complexityScale q ε⌉₊

/-- The sample-complexity statement without a possibly empty natural-number infimum.
No theorem proving this proposition is supplied by this definition. -/
def CountableCharacterization : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ (q : DiscreteLaw) (ε : ℝ), 0 < ε → ε ≤ 1 →
      (∀ n : ℕ, HasIdentityTest q ε n → c * (roundedScale q ε : ℝ) ≤ n) ∧
      (∃ n : ℕ, HasIdentityTest q ε n ∧ (n : ℝ) ≤ C * roundedScale q ε)

end IdentityTesting
