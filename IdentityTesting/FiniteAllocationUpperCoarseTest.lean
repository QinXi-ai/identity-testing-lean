import IdentityTesting.FiniteAllocationUpperParameters
import IdentityTesting.FiniteAllocationUpperCoarsening

/-! The coarse allocation test is constructed from the original finite IID
full-prefix test, with its sample count and threshold derived from KKT geometry. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting ProfileTesting

def coarseSampleConstant : ℝ := 10000000000000000000000000000000000000000

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

theorem allocation_coarse_threshold (q : Probability Ω) (x : Ω → ℝ) (T β : ℝ)
    (hT : (1 : ℝ) / 2 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hH : (coarseLabels x upperEta).Nonempty) :
    let N := ⌈coarseSampleConstant * T⌉₊
    1 ≤ N ∧ (N : ℝ) ≤ (coarseSampleConstant + 2) * T ∧
      60000 * (1 / (N : ℝ) + coarseWeightSum q x upperEta ^ ((3 : ℝ) / 4) / Real.sqrt N) ≤
        upperGap q x upperEta / 100 := by
  let N := ⌈coarseSampleConstant * T⌉₊
  let G := upperGap q x upperEta
  let R := coarseWeightSum q x upperEta ^ ((3 : ℝ) / 4)
  have hT0 : 0 < T := by linarith
  have hη : 0 < upperEta := by norm_num [upperEta]
  have hG : 0 ≤ G := upperGap_nonneg q x upperEta hx
  have hR : 0 ≤ R := Real.rpow_nonneg (coarseWeightSum_nonneg q x upperEta) _
  have hNlower : coarseSampleConstant * T ≤ (N : ℝ) := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have h : (1 : ℝ) ≤ N := by norm_num [coarseSampleConstant] at hNlower; linarith
    exact_mod_cast h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNupper : (N : ℝ) ≤ (coarseSampleConstant + 2) * T :=
    ceil_scale_le hT (by norm_num [coarseSampleConstant])
  have hrec := coarse_nonempty_reciprocal q x upperEta T β hη hT0 hβ.le hx hkkt hbudget hH
  have hrec' : upperEta / 2 ≤ T * G := hrec
  have hNG := mul_le_mul_of_nonneg_right hNlower hG
  have hbig := mul_le_mul_of_nonneg_left hrec' (by norm_num [coarseSampleConstant] : 0 ≤ coarseSampleConstant)
  have hfirst : 1 / (N : ℝ) ≤ G / 100000000 := by
    apply (div_le_iff₀ hNpos).2
    norm_num [upperEta, coarseSampleConstant] at hNG hbig
    nlinarith only [hNG, hbig]
  have hnorm := coarse_profile_norm_le q x upperEta T β hη hT0 hβ hx hkkt hbudget
  have hsη : Real.sqrt upperEta = 1 / 100000000 :=
    (Real.sqrt_eq_iff_eq_sq hη.le (by norm_num)).2 (by norm_num [upperEta])
  have hsC : Real.sqrt coarseSampleConstant = 100000000000000000000 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num [coarseSampleConstant]) (by norm_num)).2
      (by norm_num [coarseSampleConstant])
  rw [hsη] at hnorm
  have hRbound : R ≤ (200000000 * G) * Real.sqrt T := by
    have h := (div_le_iff₀ (Real.sqrt_pos.mpr hT0)).mp hnorm
    dsimp [R, G]
    nlinarith only [h]
  have hsN := Real.sqrt_le_sqrt hNlower
  rw [Real.sqrt_mul (by norm_num [coarseSampleConstant]), hsC] at hsN
  have hsNscaled := mul_le_mul_of_nonneg_left hsN (by positivity : 0 ≤ G / 100000000)
  have hsecond : R / Real.sqrt N ≤ G / 100000000 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hNpos)).2
    nlinarith only [hRbound, hsNscaled, mul_nonneg hG (Real.sqrt_nonneg T)]
  refine ⟨hN1, hNupper, ?_⟩
  change 60000 * (1 / (N : ℝ) + R / Real.sqrt N) ≤ G / 100
  linarith

theorem exists_allocation_coarse_test (q : Probability Ω) (x : Ω → ℝ) (T β : ℝ)
    (hT : (1 : ℝ) / 2 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hH : (coarseLabels x upperEta).Nonempty) :
    ∃ (N : ℕ) (test : FiniteTesting.RandomizedTest (Fin N → Ω)),
      (N : ℝ) ≤ (coarseSampleConstant + 2) * T ∧
      expectation (productLaw q N) test ≤ 1 / 100 ∧
      ∀ p : Probability Ω,
        upperGap q x upperEta / 100 <
          FiniteTesting.totalVariation (collapseLaw p (coarseLabels x upperEta))
            (collapseLaw q (coarseLabels x upperEta)) →
        1 - expectation (productLaw p N) test ≤ 1 / 100 := by
  obtain ⟨hN, hcount, hthreshold⟩ := allocation_coarse_threshold q x T β hT hβ hx hkkt hbudget hH
  obtain ⟨test, hnull, halt⟩ := exists_coarse_test q (coarseLabels x upperEta)
    ⌈coarseSampleConstant * T⌉₊ hN
  refine ⟨_, test, hcount, hnull, ?_⟩
  intro p hp
  exact halt p (lt_of_le_of_lt hthreshold hp)

end IdentityTesting.FiniteAllocationUpper
