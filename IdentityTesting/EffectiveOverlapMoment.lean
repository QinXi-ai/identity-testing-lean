import IdentityTesting.EffectiveInverseAccess
import IdentityTesting.OverlapMomentLipschitz

/-! Certified effective overlap moments for computable real atoms and a
computable positive real target. This is not restricted to rational targets. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def momentSqrtAccess {δ : ℝ} (D : EffectiveRealAccess δ) (hδ : 0 < δ)
    (b : ℚ) (hb : 0 ≤ b) : EffectiveRealAccess (Real.sqrt ((b : ℝ) / δ)) where
  approx := rationalSqrtApprox (fun n => b * D.invApprox hδ
    (oracleDyadicPrecision b (accessError n)))
  error_le := (D.ratioAccess hδ b hb).sqrtApprox_error
    (div_nonneg (by exact_mod_cast hb) hδ.le)

def finiteMomentApprox {k : ℕ} {δ : ℝ} (b : Fin k → ℚ)
    (D : EffectiveRealAccess δ) (hδ : 0 < δ) (hb : ∀ i, 0 ≤ b i) (σ : ℚ) : ℚ :=
  let n := oracleDyadicPrecision (∑ i, b i) σ
  ∑ i, b i * min 1 ((momentSqrtAccess D hδ (b i) (hb i)).approx n)

theorem finiteMomentApprox_error {k : ℕ} {δ : ℝ} (b : Fin k → ℚ)
    (D : EffectiveRealAccess δ) (hδ : 0 < δ) (hb : ∀ i, 0 ≤ b i)
    (σ : ℚ) (hσ : 0 < σ) :
    |(finiteMomentApprox b D hδ hb σ : ℝ) -
      ∑ i, (b i : ℝ) * min 1 (Real.sqrt ((b i : ℝ) / δ))| ≤ (σ : ℝ) := by
  let n := oracleDyadicPrecision (∑ i, b i) σ
  let S := fun i => momentSqrtAccess D hδ (b i) (hb i)
  have hp := oracleDyadicPrecision_spec (∑ i, b i) σ hσ
  have hpR : (∑ i, (b i : ℝ)) * (accessError n : ℝ) ≤ (σ : ℝ) := by
    have h : (∑ i, b i) * accessError n ≤ σ := by
      simpa only [accessError, n, div_eq_mul_inv, one_mul] using hp
    exact_mod_cast h
  have heach (i : Fin k) : |(b i : ℝ) * min 1 (S i |>.approx n : ℝ) -
      (b i : ℝ) * min 1 (Real.sqrt ((b i : ℝ) / δ))| ≤
      (b i : ℝ) * (accessError n : ℝ) := by
    have hm := abs_min_sub_min_le_max (1 : ℝ) (S i |>.approx n : ℝ)
      1 (Real.sqrt ((b i : ℝ) / δ))
    simp only [sub_self, abs_zero] at hm
    rw [max_eq_right (abs_nonneg ((S i |>.approx n : ℝ) -
      Real.sqrt ((b i : ℝ) / δ)))] at hm
    rw [← mul_sub, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (b i : ℝ) by exact_mod_cast hb i)]
    exact mul_le_mul_of_nonneg_left (hm.trans (S i |>.error_le n)) (by exact_mod_cast hb i)
  simp only [finiteMomentApprox, Rat.cast_sum, Rat.cast_mul, Rat.cast_min, Rat.cast_one]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(b i : ℝ) * min 1 (S i |>.approx n : ℝ) -
        (b i : ℝ) * min 1 (Real.sqrt ((b i : ℝ) / δ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (b i : ℝ) * (accessError n : ℝ) := Finset.sum_le_sum (fun i _ => heach i)
    _ = (∑ i, (b i : ℝ)) * (accessError n : ℝ) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := hpR

theorem moment_sum_extendFiniteVector {k : ℕ} (b : Fin k → ℝ)
    (hb : ∀ i, 0 ≤ b i) (δ : ℝ) :
    (∑' i, min (extendFiniteVector b i)
      ((extendFiniteVector b i) ^ (3 / 2 : ℝ) / Real.sqrt δ)) =
      ∑ i, b i * min 1 (Real.sqrt (b i / δ)) := by
  calc
    _ = ∑' i, extendFiniteVector (fun j => b j * min 1 (Real.sqrt (b j / δ))) i := by
      apply tsum_congr
      intro i
      by_cases hi : i < k
      · simp only [extendFiniteVector, dif_pos hi]
        exact overlapMoment_summand_eq_mul_min (hb ⟨i, hi⟩)
      · simp [extendFiniteVector, hi]
    _ = _ := (extendFiniteVector_hasSum _).tsum_eq

def countableMomentApprox {a : ℕ → ℝ} {δ : ℝ} (A : EffectiveMassAccess a)
    (D : EffectiveRealAccess δ) (hδ : 0 < δ) (σ : ℚ) (hσ : 0 < σ) : ℚ :=
  let b := A.finiteApprox (σ / 3) (by positivity)
  finiteMomentApprox b D hδ (fun i => (A.finiteApprox_pos _ _ i).le) (σ / 2)

theorem countableMomentApprox_error {a : ℕ → ℝ} {δ : ℝ}
    (A : EffectiveMassAccess a) (D : EffectiveRealAccess δ) (hδ : 0 < δ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (σ : ℚ) (hσ : 0 < σ) :
    |(countableMomentApprox A D hδ σ hσ : ℝ) -
      ∑' i, min (a i) ((a i) ^ (3 / 2 : ℝ) / Real.sqrt δ)| ≤ (σ : ℝ) := by
  let b := A.finiteApprox (σ / 3) (by positivity)
  have hb : ∀ i, 0 ≤ b i := fun i => (A.finiteApprox_pos _ _ i).le
  have hbR : ∀ i, 0 ≤ (b i : ℝ) := fun i => by exact_mod_cast hb i
  have hfinite := finiteMomentApprox_error b D hδ hb (σ / 2) (half_pos hσ)
  have hlip := overlapMoment_sum_abs_sub_le ha (extendFiniteVector_nonneg hbR)
    hs (extendFiniteVector_hasSum _).summable hδ
  rw [moment_sum_extendFiniteVector _ hbR] at hlip
  have hl1 := A.finiteApprox_l1 ha hs (σ / 3) (by positivity)
  have hbound : |(∑' i, min (a i) ((a i) ^ (3 / 2 : ℝ) / Real.sqrt δ)) -
      ∑ i, (b i : ℝ) * min 1 (Real.sqrt ((b i : ℝ) / δ))| ≤ (σ : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hl1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    push_cast at h
    exact hlip.trans (by linarith)
  change |(finiteMomentApprox b D hδ hb (σ / 2) : ℝ) - _| ≤ _
  have htri := abs_sub_le (finiteMomentApprox b D hδ hb (σ / 2) : ℝ)
    (∑ i, (b i : ℝ) * min 1 (Real.sqrt ((b i : ℝ) / δ)))
    (∑' i, min (a i) ((a i) ^ (3 / 2 : ℝ) / Real.sqrt δ))
  rw [abs_sub_comm] at hbound
  push_cast at hfinite
  linarith

def countableMomentInterval {a : ℕ → ℝ} {δ : ℝ} (A : EffectiveMassAccess a)
    (D : EffectiveRealAccess δ) (hδ : 0 < δ) (σ : ℚ) (hσ : 0 < σ) : ℚ × ℚ :=
  let x := countableMomentApprox A D hδ (σ / 2) (half_pos hσ)
  (x - σ / 2, x + σ / 2)

theorem countableMomentInterval_spec {a : ℕ → ℝ} {δ : ℝ}
    (A : EffectiveMassAccess a) (D : EffectiveRealAccess δ) (hδ : 0 < δ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (σ : ℚ) (hσ : 0 < σ) :
    OracleIntervalValid (∑' i, min (a i) ((a i) ^ (3 / 2 : ℝ) / Real.sqrt δ)) σ
      (countableMomentInterval A D hδ σ hσ) := by
  have h := abs_le.mp (countableMomentApprox_error A D hδ ha hs (σ / 2) (half_pos hσ))
  simp only [OracleIntervalValid, countableMomentInterval, Rat.cast_add,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
  push_cast at h
  exact ⟨by linarith, by linarith, by ring_nf; exact le_rfl⟩

theorem overlapMoment_effective_interval (q : DiscreteLaw) (A : EffectiveMassAccess q.mass)
    {δ : ℝ} (D : EffectiveRealAccess δ) (hδ : 0 < δ) (σ : ℚ) (hσ : 0 < σ) :
    OracleIntervalValid (overlapMoment q δ) σ (countableMomentInterval A D hδ σ hσ) :=
  countableMomentInterval_spec A D hδ q.nonneg q.summable σ hσ

end IdentityTesting.RationalComputation
