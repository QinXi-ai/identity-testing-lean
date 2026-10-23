import IdentityTesting.HeavyUpperParameters
import Mathlib.Analysis.MeanInequalitiesPow

/-! The actual coarse heavy-head test and its threshold at the heavy root. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper ProfileTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem retained_profile_sum (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (η : ℝ)
    (ha : x a = 1) (hη : 0 ≤ η) :
    weightSum (collapseLaw q (retainedLabels a x η)) (some a) =
      coarseWeightSum (tailWeights q a) x η +
        (∑ i ∈ fineLabels a x η, q.mass i) ^ ((2 : ℝ) / 3) := by
  let Q := collapseLaw q (retainedLabels a x η)
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Option Ω)))
    (f := fun i => Q.mass i ^ ((2 : ℝ) / 3)) (Finset.mem_univ none)
  have ha' := Finset.sum_erase_add (s := (Finset.univ : Finset (Option Ω)))
    (f := fun i => Q.mass i ^ ((2 : ℝ) / 3)) (Finset.mem_univ (some a))
  change weightSum Q none + Q.mass none ^ ((2 : ℝ) / 3) = _ at hs
  change weightSum Q (some a) + Q.mass (some a) ^ ((2 : ℝ) / 3) = _ at ha'
  have hnone : Q.mass none = ∑ i ∈ fineLabels a x η, q.mass i := by
    dsimp only [Q]
    rw [collapseLaw_mass_none, retained_complement]
  have hhead : Q.mass (some a) = q.mass a := by
    simp only [Q, collapseLaw_mass_some, retainedLabels, Finset.mem_insert_self, if_true]
  have hweight : weightSum Q none = q.mass a ^ ((2 : ℝ) / 3) +
      coarseWeightSum (tailWeights q a) x η := by
    dsimp only [Q]
    rw [collapseLaw_weightSum, retainedLabels, Finset.sum_insert (head_not_coarse a x η ha hη),
      tail_coarseWeightSum q a x η ha hη]
  rw [hweight, hnone] at hs
  rw [hhead] at ha'
  change weightSum Q (some a) = _
  linarith

theorem heavy_coarse_threshold (Q : TailWeights Ω) (x : Ω → ℝ) (T β g r : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g) (hr : 0 ≤ r)
    (hrscale : Real.sqrt r ≤ g * Real.sqrt T)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, Q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, Q.mass i * x i * (1 - x i ^ 4)) :
    let N := ⌈coarseSampleConstant * T⌉₊
    1 ≤ N ∧ (N : ℝ) ≤ (coarseSampleConstant + 2) * T ∧
      60000 * (1 / (N : ℝ) +
        (coarseWeightSum Q x upperEta + r ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) / Real.sqrt N) ≤
        (upperGap Q x upperEta + g) / 100 := by
  let N := ⌈coarseSampleConstant * T⌉₊
  let G := upperGap Q x upperEta
  let B := G + g
  let S := coarseWeightSum Q x upperEta
  let Z := (S + r ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4)
  have hT0 : 0 < T := by linarith
  have hη : 0 < upperEta := by norm_num [upperEta]
  have hG : 0 ≤ G := upperGap_nonneg Q x upperEta hx
  have hB : 0 ≤ B := add_nonneg hG hg
  have hS : 0 ≤ S := coarseWeightSum_nonneg Q x upperEta
  have hNlower : coarseSampleConstant * T ≤ (N : ℝ) := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have h : (1 : ℝ) ≤ N := by norm_num [coarseSampleConstant] at hNlower; linarith
    exact_mod_cast h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNupper : (N : ℝ) ≤ (coarseSampleConstant + 2) * T :=
    ceil_scale_le (by linarith) (by norm_num [coarseSampleConstant])
  have hrec : 1 ≤ T * B := by dsimp [B]; nlinarith [mul_nonneg hT0.le hG]
  have hNB := mul_le_mul_of_nonneg_right hNlower hB
  have hbig := mul_le_mul_of_nonneg_left hrec (by norm_num [coarseSampleConstant] : 0 ≤ coarseSampleConstant)
  have hfirst : 1 / (N : ℝ) ≤ B / 100000000 := by
    apply (div_le_iff₀ hNpos).2
    norm_num [coarseSampleConstant] at hNB hbig
    nlinarith only [hNB, hbig]
  have hnorm := coarse_profile_norm_le Q x upperEta T β hη hT0 hβ hx hkkt hbudget
  have hsη : Real.sqrt upperEta = 1 / 100000000 :=
    (Real.sqrt_eq_iff_eq_sq hη.le (by norm_num)).2 (by norm_num [upperEta])
  have hsC : Real.sqrt coarseSampleConstant = 100000000000000000000 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num [coarseSampleConstant]) (by norm_num)).2
      (by norm_num [coarseSampleConstant])
  rw [hsη] at hnorm
  have hSbound : S ^ ((3 : ℝ) / 4) ≤ (200000000 * G) * Real.sqrt T := by
    have h := (div_le_iff₀ (Real.sqrt_pos.mpr hT0)).mp hnorm
    dsimp [S, G]
    nlinarith only [h]
  have hsub := Real.rpow_add_le_add_rpow hS (Real.rpow_nonneg hr ((2 : ℝ) / 3))
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 : ℝ) / 4 ≤ 1)
  have hpow : (r ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 4) = Real.sqrt r := by
    rw [← Real.rpow_mul hr]
    norm_num
    exact (Real.sqrt_eq_rpow r).symm
  rw [hpow] at hsub
  have hZ : Z ≤ (200000001 * B) * Real.sqrt T := by
    change Z ≤ S ^ ((3 : ℝ) / 4) + Real.sqrt r at hsub
    dsimp [B]
    nlinarith [mul_nonneg hG (Real.sqrt_nonneg T), mul_nonneg hg (Real.sqrt_nonneg T)]
  have hsN := Real.sqrt_le_sqrt hNlower
  rw [Real.sqrt_mul (by norm_num [coarseSampleConstant]), hsC] at hsN
  have hsNscaled := mul_le_mul_of_nonneg_left hsN (by positivity : 0 ≤ B / 100000000)
  have hsecond : Z / Real.sqrt N ≤ B / 100000000 := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hNpos)).2
    nlinarith only [hZ, hsNscaled, mul_nonneg hB (Real.sqrt_nonneg T)]
  refine ⟨hN1, hNupper, ?_⟩
  change 60000 * (1 / (N : ℝ) + Z / Real.sqrt N) ≤ B / 100
  linarith

theorem exists_heavy_coarse_test (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (T β g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hrscale : Real.sqrt (1 - q.mass a) ≤ g * Real.sqrt T)
    (ha : x a = 1) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4)) :
    ∃ (N : ℕ) (test : FiniteTesting.RandomizedTest (Fin N → Ω)),
      (N : ℝ) ≤ (coarseSampleConstant + 2) * T ∧
      expectation (productLaw q N) test ≤ 1 / 100 ∧
      ∀ p : Probability Ω,
        (upperGap (tailWeights q a) x upperEta + g) / 100 <
          FiniteTesting.totalVariation (collapseLaw p (retainedLabels a x upperEta))
            (collapseLaw q (retainedLabels a x upperEta)) →
        1 - expectation (productLaw p N) test ≤ 1 / 100 := by
  have hr : 0 ≤ ∑ i ∈ fineLabels a x upperEta, q.mass i := Finset.sum_nonneg (fun i _ => q.nonneg i)
  have hrs := (Real.sqrt_le_sqrt (fine_mass_le_tail q a x upperEta)).trans hrscale
  obtain ⟨hN, hcount, hthreshold⟩ := heavy_coarse_threshold (tailWeights q a) x T β g
    (∑ i ∈ fineLabels a x upperEta, q.mass i) hT hβ hg hTg hr hrs hx hkkt hbudget
  let N := ⌈coarseSampleConstant * T⌉₊
  let H := retainedLabels a x upperEta
  obtain ⟨test, hnull, halt⟩ := fullPrefix_identity_test (collapseLaw q H) (some a) N hN
  refine ⟨N, mappedTest (fun sample => collapseMap H ∘ sample) test, hcount, ?_, ?_⟩
  · rw [expectation_collapse_sample]
    exact hnull
  · intro p hp
    rw [expectation_collapse_sample]
    apply halt (collapseLaw p H)
    have hh := lt_of_le_of_lt hthreshold hp
    simpa only [profileRadius, H, retained_profile_sum q a x upperEta ha (by norm_num [upperEta])] using hh

end IdentityTesting.HeavyUpper
