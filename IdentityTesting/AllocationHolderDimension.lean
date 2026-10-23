import IdentityTesting.AllocationHolderBound

/-! Dimension-dependent bound on the finite allocation Hölder envelope. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem finite_holder_dimension_bound {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤
      Real.sqrt k * ∑ i, a i := by
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i : Fin k => a i ^ (2 / 3 : ℝ)) (g := fun _ => (1 : ℝ)) hpq
    (fun i _ => Real.rpow_nonneg (ha i) _) (fun _ _ => by norm_num)
  have hf (i : Fin k) : (a i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = a i := by
    rw [← Real.rpow_mul (ha i)]
    norm_num
  simp_rw [hf] at hh
  norm_num at hh
  have hsum : 0 ≤ ∑ i, a i ^ (2 / 3 : ℝ) :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (ha i) _)
  have hmass : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  have hb := Real.rpow_le_rpow hsum hh (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (Real.rpow_nonneg hmass _) (Real.rpow_nonneg (Nat.cast_nonneg k) _),
    ← Real.rpow_mul hmass, ← Real.rpow_mul (Nat.cast_nonneg k)] at hb
  norm_num at hb
  rw [Real.sqrt_eq_rpow]
  nlinarith only [hb]

end IdentityTesting
