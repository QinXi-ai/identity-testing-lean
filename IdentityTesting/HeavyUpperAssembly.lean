import IdentityTesting.HeavyUpperCoarseTest

/-! Actual heavy-head test assembly on the original finite IID samples. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyUpper
open FiniteTesting FiniteAllocationUpper ProfileTesting
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem small_coarse_distance_overlap (p q : Probability Ω) (a : Ω) (x : Ω → ℝ) (ε g : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hg : 0 ≤ g)
    (hradius : (∑ i, (tailWeights q a).mass i * x i) + g = ε)
    (halt : ε < FiniteTesting.totalVariation p q)
    (hcoarse : FiniteTesting.totalVariation (collapseLaw p (retainedLabels a x upperEta))
      (collapseLaw q (retainedLabels a x upperEta)) ≤
        (upperGap (tailWeights q a) x upperEta + g) / 100) :
    localOverlap p q (fineLabels a x upperEta) ≤
      2 * concentratedResidual (tailWeights q a) x upperEta := by
  have hid := totalVariation_collapse_identity p q (retainedLabels a x upperEta)
  rw [retained_complement] at hid
  have hr := tail_radius_split q a x upperEta ε g hradius
  have hmin := min_le_right (∑ i ∈ fineLabels a x upperEta, p.mass i)
    (∑ i ∈ fineLabels a x upperEta, q.mass i)
  have hD := coarseDisplacement_nonneg (tailWeights q a) x upperEta (fun i => (hx i).1)
  have hE := concentratedResidual_nonneg (tailWeights q a) x upperEta (fun i => (hx i).2)
  dsimp [upperGap] at hcoarse
  linarith

theorem coarse_only_alternative (p q : Probability Ω) (a : Ω) (x : Ω → ℝ) (ε g : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hg : 0 < g)
    (hradius : (∑ i, (tailWeights q a).mass i * x i) + g = ε)
    (hcase : 2 * concentratedResidual (tailWeights q a) x upperEta ≤
      coarseDisplacement (tailWeights q a) x upperEta + g)
    (halt : ε < FiniteTesting.totalVariation p q) :
    (upperGap (tailWeights q a) x upperEta + g) / 100 <
      FiniteTesting.totalVariation (collapseLaw p (retainedLabels a x upperEta))
        (collapseLaw q (retainedLabels a x upperEta)) := by
  by_contra hn
  have hc := le_of_not_gt hn
  have hid := totalVariation_collapse_identity p q (retainedLabels a x upperEta)
  rw [retained_complement] at hid
  have hr := tail_radius_split q a x upperEta ε g hradius
  have hmin := min_le_right (∑ i ∈ fineLabels a x upperEta, p.mass i)
    (∑ i ∈ fineLabels a x upperEta, q.mass i)
  have hD := coarseDisplacement_nonneg (tailWeights q a) x upperEta (fun i => (hx i).1)
  have hE := concentratedResidual_nonneg (tailWeights q a) x upperEta (fun i => (hx i).2)
  have hO : 0 ≤ localOverlap p q (fineLabels a x upperEta) :=
    Finset.sum_nonneg (fun i _ => le_min (p.nonneg i) (q.nonneg i))
  dsimp [upperGap] at hc
  linarith

theorem finite_heavy_test_of_kkt (q : Probability Ω) (a : Ω) (x : Ω → ℝ) (T β ε g : ℝ)
    (hT : 4 ≤ T) (hβ : 0 < β) (hg : 0 ≤ g) (hTg : 1 ≤ T * g)
    (hrscale : Real.sqrt (1 - q.mass a) ≤ g * Real.sqrt T)
    (ha : x a = 1) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, (tailWeights q a).mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, (tailWeights q a).mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, (tailWeights q a).mass i * x i) + g = ε) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)),
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * T ∧
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      ∀ p : Probability Ω, ε < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3 := by
  have hT0 : 0 ≤ T := by linarith
  have hg0 : 0 < g := by
    by_contra hn
    have hz : g = 0 := le_antisymm (le_of_not_gt hn) hg
    rw [hz] at hTg
    norm_num at hTg
  obtain ⟨N, coarse, hN, hnull, hcoarse⟩ :=
    exists_heavy_coarse_test q a x T β g hT hβ hg hTg hrscale ha hx hkkt hbudget
  by_cases hcase : coarseDisplacement (tailWeights q a) x upperEta + g <
      2 * concentratedResidual (tailWeights q a) x upperEta
  · obtain ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hcoll, hscale⟩ :=
      heavy_actual_parameters q a x T β g hT hβ hg hTg hx hkkt hbudget hcase
    let m := ⌈10000 * T⌉₊
    let fine := weightedMeanRepeatTest q (fineLabels a x upperEta) m
    let joined := testMaximum (firstBlockTest N m coarse) (secondBlockTest N m fine)
    have hm0 : 0 < m := by omega
    have hm : (m : ℝ) ≤ 10002 * T := by
      simpa only [m, show (10000 : ℝ) + 2 = 10002 by norm_num] using
        ceil_scale_le (by linarith : (1 : ℝ) / 2 ≤ T) (by norm_num : (0 : ℝ) ≤ 10000)
    have hfnull := weightedMeanRepeatTest_null_error q (fineLabels a x upperEta)
      m w hm0 hA hw hmean hcoll
    refine ⟨N + m, joined, ?_, ?_, ?_⟩
    · rw [Nat.cast_add]
      nlinarith only [hN, hm]
    · have hjoin := expectation_testMaximum_le (productLaw q (N + m))
        (firstBlockTest N m coarse) (secondBlockTest N m fine)
      rw [expectation_firstBlockTest, expectation_secondBlockTest] at hjoin
      change expectation (productLaw q (N + m)) (testMaximum _ _) ≤ _
      change expectation (productLaw q m) fine ≤ 1 / 10 at hfnull
      linarith
    · intro p hp
      by_cases hc : (upperGap (tailWeights q a) x upperEta + g) / 100 <
          FiniteTesting.totalVariation (collapseLaw p (retainedLabels a x upperEta))
            (collapseLaw q (retainedLabels a x upperEta))
      · have ht := hcoarse p hc
        have hdom := expectation_le_testMaximum_left (productLaw p (N + m))
          (firstBlockTest N m coarse) (secondBlockTest N m fine)
        rw [expectation_firstBlockTest] at hdom
        change 1 - expectation (productLaw p (N + m)) (testMaximum _ _) ≤ _
        linarith
      · have hO := small_coarse_distance_overlap p q a x ε g hx hg hradius hp (le_of_not_gt hc)
        have hf := weightedMeanRepeatTest_alternative_error p q (fineLabels a x upperEta)
          m w (concentratedResidual (tailWeights q a) x upperEta) hm2 hw0 hE hA hw hmean hsmall hO hscale
        have hdom := expectation_le_testMaximum_right (productLaw p (N + m))
          (firstBlockTest N m coarse) (secondBlockTest N m fine)
        rw [expectation_secondBlockTest] at hdom
        change 1 - expectation (productLaw p m) fine ≤ 1 / 20 at hf
        change 1 - expectation (productLaw p (N + m)) (testMaximum _ _) ≤ _
        linarith
  · refine ⟨N, coarse, ?_, hnull.trans (by norm_num), ?_⟩
    · nlinarith only [hN, hT0]
    · intro p hp
      exact (hcoarse p (coarse_only_alternative p q a x ε g hx hg0 hradius
        (le_of_not_gt hcase) hp)).trans (by norm_num)

end IdentityTesting.HeavyUpper
