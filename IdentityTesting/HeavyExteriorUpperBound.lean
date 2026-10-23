import IdentityTesting.EventCounts
import IdentityTesting.FiniteAllocationUpper
import IdentityTesting.CountablePooling

/-! An actual count test above the tail-mass boundary, with arbitrary labels
and zero reference masses allowed. -/
noncomputable section
namespace IdentityTesting.HeavyExteriorTesting
open scoped BigOperators
open Classical FiniteTesting EventCounts

theorem tail_event_mass {Ω : Type*} [Fintype Ω] (p : Probability Ω) (head : Ω) :
    eventMass p ({head}ᶜ : Finset Ω) = 1 - p.mass head := by
  have h := Finset.sum_add_sum_compl ({head} : Finset Ω) p.mass
  rw [Finset.sum_singleton, p.total] at h
  unfold eventMass
  linarith

theorem exterior_tail_gap {Ω : Type*} [Fintype Ω] (q p : Probability Ω) (head : Ω)
    (Δ : ℝ) (hΔ : 0 < Δ) (hsep : 1 - q.mass head + Δ < FiniteTesting.totalVariation p q) :
    Δ < |eventMass p ({head}ᶜ : Finset Ω) - eventMass q ({head}ᶜ : Finset Ω)| := by
  have hsum : min (p.mass head) (q.mass head) ≤ ∑ i, min (p.mass i) (q.mass i) :=
    Finset.single_le_sum (fun i _ => le_min (p.nonneg i) (q.nonneg i)) (Finset.mem_univ head)
  have htv : FiniteTesting.totalVariation p q ≤ 1 - min (p.mass head) (q.mass head) := by
    rw [finite_totalVariation_eq_one_sub_overlap]
    linarith
  have hhead : p.mass head < q.mass head := by
    by_contra h
    rw [min_eq_right (le_of_not_gt h)] at htv
    linarith
  rw [min_eq_left hhead.le] at htv
  rw [tail_event_mass, tail_event_mass]
  have habs := le_abs_self ((1 - p.mass head) - (1 - q.mass head))
  linarith

theorem exterior_sample_parameters (R Δ : ℝ) (hR : 0 ≤ R)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    let n := ⌈1000000 * (R / Δ ^ 2 + 1 / Δ)⌉₊
    0 < n ∧ (n : ℝ) ≤ 1000001 * (R / Δ ^ 2 + 1 / Δ) ∧
      2 * countThreshold n R 20 ≤ Δ := by
  let K := R / Δ ^ 2 + 1 / Δ
  let n := ⌈1000000 * K⌉₊
  have hK : 1 ≤ K := by
    have hdiv : (1 : ℝ) ≤ 1 / Δ := (le_div_iff₀ hΔ).mpr (by linarith)
    have hnon := div_nonneg hR (sq_nonneg Δ)
    dsimp only [K]
    linarith
  have hbase : 1000000 * K ≤ (n : ℝ) := Nat.le_ceil _
  have hnR : (0 : ℝ) < n := by linarith
  have hn : 0 < n := Nat.cast_pos.mp hnR
  have hupper : (n : ℝ) ≤ 1000001 * K := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 1000000 * K by positivity)
    change (n : ℝ) < 1000000 * K + 1 at h
    linarith
  have hpart₁ : 1000000 * (R / Δ ^ 2) ≤ (n : ℝ) := by
    have h := one_div_pos.mpr hΔ
    dsimp only [K] at hbase
    linarith
  have hpart₂ : 1000000 / Δ ≤ (n : ℝ) := by
    have h := div_nonneg hR (sq_nonneg Δ)
    dsimp only [K] at hbase
    rw [show (1000000 : ℝ) / Δ = 1000000 * (1 / Δ) by ring]
    linarith
  have hsquared : 1000000 * R ≤ (n : ℝ) * Δ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hΔ)).mp
    simpa only [mul_div_assoc] using hpart₁
  have hlinear : 1000000 ≤ (n : ℝ) * Δ := (div_le_iff₀ hΔ).mp hpart₂
  have hratio : R / (n : ℝ) ≤ (Δ / 1000) ^ 2 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hsquared]
  have hsqrt : Real.sqrt (R / (n : ℝ)) ≤ Δ / 1000 := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < Δ / 1000)] using
      Real.sqrt_le_sqrt hratio
  have hinv : 1 / (n : ℝ) ≤ Δ / 1000 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hlinear]
  refine ⟨hn, hupper, ?_⟩
  unfold countThreshold
  linarith

theorem finite_exterior_count_test {Ω : Type*} [Fintype Ω]
    (q : Probability Ω) (head : Ω) (Δ : ℝ) (hΔ : 0 < Δ)
    (he1 : 1 - q.mass head + Δ < 1) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)),
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      (∀ p : Probability Ω, 1 - q.mass head + Δ < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3) ∧
      (n : ℝ) ≤ 1000001 * ((1 - q.mass head) / Δ ^ 2 + 1 / Δ) := by
  have hR : 0 ≤ 1 - q.mass head := by
    rw [← tail_event_mass q head]
    exact eventMass_nonneg q _
  have hΔ1 : Δ < 1 := by linarith
  obtain ⟨hn, hnupper, hnsep⟩ := exterior_sample_parameters (1 - q.mass head) Δ hR hΔ hΔ1
  let n := ⌈1000000 * ((1 - q.mass head) / Δ ^ 2 + 1 / Δ)⌉₊
  let E : Finset Ω := {head}ᶜ
  refine ⟨n, countTest E n (eventMass q E) 20, ?_, ?_, hnupper⟩
  · exact (countTest_null_error q E n 20 hn (by norm_num)).trans (by norm_num)
  · intro p hp
    apply (countTest_alternative_error q p E n 20 hn (by norm_num) ?_).trans (by norm_num)
    have hgap := exterior_tail_gap q p head Δ hΔ hp
    have hE : eventMass q E = 1 - q.mass head := tail_event_mass q head
    change Δ < |eventMass p E - eventMass q E| at hgap
    rw [hE] at hgap
    rw [hE]
    exact hnsep.trans hgap.le

theorem finite_exterior_count_upper {k : ℕ} (q : Probability (Fin k))
    (head : Fin k) (Δ : ℝ) (hΔ : 0 < Δ) (he1 : 1 - q.mass head + Δ < 1) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) (1 - q.mass head + Δ) n ∧
      (n : ℝ) ≤ 1000001 * ((1 - q.mass head) / Δ ^ 2 + 1 / Δ) := by
  let Q := pooledLaw (extendFiniteLaw q) (Finset.range k)
  let j : PoolLabel (Finset.range k) := some (FiniteAllocationUpper.rangeIndexEquiv k head)
  have hj : Q.mass j = q.mass head := by
    simp only [Q, j, FiniteAllocationUpper.finite_pooled_mass_some, Equiv.symm_apply_apply]
  obtain ⟨n, test, hnull, halt, hn⟩ := finite_exterior_count_test Q j Δ hΔ (by rwa [hj])
  rw [hj] at halt hn
  refine ⟨n, ?_, hn⟩
  apply hasIdentityTest_of_pooled_test (extendFiniteLaw q) (Finset.range k)
    (1 - q.mass head + Δ) n test hnull
  rw [FiniteAllocationUpper.finite_reference_residual_zero, sub_zero]
  exact halt

end IdentityTesting.HeavyExteriorTesting
