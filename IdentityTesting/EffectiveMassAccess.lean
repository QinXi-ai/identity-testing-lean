import IdentityTesting.AllocationMassLipschitz
import IdentityTesting.CountableAllocationApproximation
import IdentityTesting.RationalAllocationOracle
import IdentityTesting.CertifiedNatSearch

/-! Executable access to computable atoms and certified vanishing tails.
The tail modulus is found by rational decidable search, not supplied as data. -/
open scoped BigOperators
open Filter Topology
namespace IdentityTesting.RationalComputation

def accessError (n : ℕ) : ℚ := 1 / 2 ^ n

theorem accessError_pos (n : ℕ) : 0 < accessError n := by
  unfold accessError
  positivity

structure EffectiveRealAccess (x : ℝ) where
  approx : ℕ → ℚ
  error_le : ∀ n, |(approx n : ℝ) - x| ≤ (accessError n : ℝ)

structure EffectiveMassAccess (a : ℕ → ℝ) where
  atomApprox : ℕ → ℕ → ℚ
  atom_error_le : ∀ i n, |(atomApprox i n : ℝ) - a i| ≤ (accessError n : ℝ)
  tailBound : ℕ → ℚ
  tail_nonneg : ∀ m, 0 ≤ tailBound m
  tail_le : ∀ m, discardedMass a (Finset.range m) ≤ (tailBound m : ℝ)
  tail_tendsto : Tendsto (fun m => (tailBound m : ℝ)) atTop (𝓝 0)

theorem EffectiveMassAccess.exists_tail_index {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, A.tailBound (m + 1) ≤ ε := by
  have ht := A.tail_tendsto.comp (tendsto_add_atTop_nat 1)
  obtain ⟨m, hm⟩ := (ht.eventually_lt_const
    (show (0 : ℝ) < (ε : ℝ) by exact_mod_cast hε)).exists
  change (A.tailBound (m + 1) : ℝ) < (ε : ℝ) at hm
  exact ⟨m, by exact_mod_cast hm.le⟩

/-- This certified search uses only the decidable comparison of rational numbers.
The convergence proof is erased and does not choose the returned index. -/
def EffectiveMassAccess.tailIndex {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  (certifiedNatSearch _ (A.exists_tail_index ε hε)).val

theorem EffectiveMassAccess.tailIndex_spec {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) :
    A.tailBound (A.tailIndex ε hε + 1) ≤ ε :=
  certifiedNatSearch_spec _ (A.exists_tail_index ε hε)

def EffectiveMassAccess.positivePrefix {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (m n : ℕ) (i : Fin (m + 1)) : ℚ :=
  max (A.atomApprox i.val n) 0 + accessError n

theorem EffectiveMassAccess.positivePrefix_pos {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (m n : ℕ) (i : Fin (m + 1)) :
    0 < A.positivePrefix m n i :=
  add_pos_of_nonneg_of_pos (le_max_right _ _) (accessError_pos n)

theorem EffectiveMassAccess.positivePrefix_error {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ha : ∀ i, 0 ≤ a i) (m n : ℕ) (i : Fin (m + 1)) :
    |a i.val - (A.positivePrefix m n i : ℝ)| ≤ 2 * (accessError n : ℝ) := by
  have h := (abs_le.mp (A.atom_error_le i.val n))
  have he : (0 : ℝ) < (accessError n : ℝ) := by exact_mod_cast accessError_pos n
  simp only [EffectiveMassAccess.positivePrefix, Rat.cast_add, Rat.cast_max, Rat.cast_zero]
  rw [abs_le]
  by_cases hx : (A.atomApprox i.val n : ℝ) ≤ 0
  · rw [max_eq_right hx]
    constructor <;> linarith [ha i.val]
  · rw [max_eq_left (le_of_not_ge hx)]
    constructor <;> linarith

theorem EffectiveMassAccess.positivePrefix_l1 {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (m n : ℕ) :
    (∑' i, |a i - extendFiniteVector (fun j => (A.positivePrefix m n j : ℝ)) i|) ≤
      (A.tailBound (m + 1) : ℝ) + 2 * (m + 1) * (accessError n : ℝ) := by
  let b := extendFiniteVector (fun j => (A.positivePrefix m n j : ℝ))
  have hbs : Summable b := (extendFiniteVector_hasSum _).summable
  have hsum := (hs.sub hbs).abs.sum_add_tsum_compl (s := Finset.range (m + 1))
  change (∑ i ∈ Finset.range (m + 1), |a i - b i|) +
    (∑' i : {i // i ∉ Finset.range (m + 1)}, |a i - b i|) =
    ∑' i, |a i - b i| at hsum
  have htail : (∑' i : {i // i ∉ Finset.range (m + 1)}, |a i - b i|) =
      discardedMass a (Finset.range (m + 1)) := by
    apply tsum_congr
    intro i
    have hi : ¬ i.val < m + 1 := by simpa only [Finset.mem_range] using i.property
    simp only [b, extendFiniteVector, dif_neg hi, sub_zero, abs_of_nonneg (ha i)]
  have hp : (∑ i ∈ Finset.range (m + 1), |a i - b i|) ≤
      (m + 1) * (2 * (accessError n : ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (m + 1), 2 * (accessError n : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [b, extendFiniteVector, dif_pos hi'] using
          A.positivePrefix_error ha m n ⟨i, hi'⟩
      _ = _ := by simp
  rw [htail] at hsum
  change (∑' i, |a i - b i|) ≤ _
  linarith [A.tail_le (m + 1)]

def EffectiveMassAccess.prefixIndex {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  A.tailIndex (ε / 2) (half_pos hε)

def EffectiveMassAccess.atomPrecision {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  oracleDyadicPrecision (2 * (A.prefixIndex ε hε + 1)) (ε / 2)

def EffectiveMassAccess.finiteApprox {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) :
    Fin (A.prefixIndex ε hε + 1) → ℚ :=
  A.positivePrefix (A.prefixIndex ε hε) (A.atomPrecision ε hε)

theorem EffectiveMassAccess.finiteApprox_pos {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ε : ℚ) (hε : 0 < ε) (i) :
    0 < A.finiteApprox ε hε i := A.positivePrefix_pos _ _ i

theorem EffectiveMassAccess.finiteApprox_l1 {a : ℕ → ℝ}
    (A : EffectiveMassAccess a) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (ε : ℚ) (hε : 0 < ε) :
    (∑' i, |a i - extendFiniteVector (fun j => (A.finiteApprox ε hε j : ℝ)) i|) ≤
      (ε : ℝ) := by
  have ht := A.tailIndex_spec (ε / 2) (half_pos hε)
  have hp := oracleDyadicPrecision_spec (2 * (A.prefixIndex ε hε + 1))
    (ε / 2) (half_pos hε)
  have htR : (A.tailBound (A.prefixIndex ε hε + 1) : ℝ) ≤ (ε : ℝ) / 2 := by
    exact_mod_cast ht
  have hpR : 2 * (A.prefixIndex ε hε + 1 : ℕ) *
      (accessError (A.atomPrecision ε hε) : ℝ) ≤ (ε : ℝ) / 2 := by
    have hQ : 2 * (A.prefixIndex ε hε + 1 : ℚ) *
        accessError (A.atomPrecision ε hε) ≤ ε / 2 := by
      simpa only [accessError, EffectiveMassAccess.atomPrecision, div_eq_mul_inv,
        one_mul] using hp
    exact_mod_cast hQ
  have h := A.positivePrefix_l1 ha hs (A.prefixIndex ε hε) (A.atomPrecision ε hε)
  change (∑' i, |a i - extendFiniteVector
    (fun j => (A.positivePrefix _ _ j : ℝ)) i|) ≤ _
  push_cast at hpR
  linarith

end IdentityTesting.RationalComputation
