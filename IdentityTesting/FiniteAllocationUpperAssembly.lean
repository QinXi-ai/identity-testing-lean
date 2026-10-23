import IdentityTesting.FiniteAllocationUpperCoarseTest

/-! Assembly of actual coarse and concentrated tests. The final original-root
caller supplies KKT coordinates constructed from the actual optimizer. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.FiniteAllocationUpper
open FiniteTesting FiniteIID ProfileTesting EventCounts

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

def secondBlockTest (m n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)) :
    FiniteTesting.RandomizedTest (Fin (m + n) → Ω) where
  reject sample := test.reject (secondBlock m n sample)
  nonneg _ := test.nonneg _
  le_one _ := test.le_one _

omit [DecidableEq Ω] in
theorem expectation_secondBlockTest (p : Probability Ω) (m n : ℕ)
    (test : FiniteTesting.RandomizedTest (Fin n → Ω)) :
    expectation (productLaw p (m + n)) (secondBlockTest m n test) =
      expectation (productLaw p n) test := by
  have h := mean_productLaw_blocks p m n (fun _ right => test.reject right)
  rw [mean_const] at h
  exact h

theorem small_coarse_distance_overlap (p q : Probability Ω) (x : Ω → ℝ) (ε : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hradius : (∑ i, q.mass i * x i) = ε)
    (halt : ε < FiniteTesting.totalVariation p q)
    (hcoarse : FiniteTesting.totalVariation (collapseLaw p (coarseLabels x upperEta))
      (collapseLaw q (coarseLabels x upperEta)) ≤ upperGap q x upperEta / 100) :
    localOverlap p q (concentratedLabels x upperEta) ≤ 2 * concentratedResidual q x upperEta := by
  have hid := totalVariation_collapse_identity p q (coarseLabels x upperEta)
  have hr := allocation_radius_split q x upperEta ε hradius
  have hmin := min_le_right (∑ i ∈ concentratedLabels x upperEta, p.mass i)
    (∑ i ∈ concentratedLabels x upperEta, q.mass i)
  have hD := coarseDisplacement_nonneg q x upperEta (fun i => (hx i).1)
  have hE := concentratedResidual_nonneg q x upperEta (fun i => (hx i).2)
  dsimp [concentratedLabels] at hmin ⊢
  dsimp [upperGap] at hcoarse
  dsimp [concentratedLabels] at hr hE hcoarse
  linarith

theorem coarse_only_alternative (p q : Probability Ω) (x : Ω → ℝ) (ε : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hradius : (∑ i, q.mass i * x i) = ε)
    (hD : 2 * concentratedResidual q x upperEta < coarseDisplacement q x upperEta)
    (halt : ε < FiniteTesting.totalVariation p q) :
    upperGap q x upperEta / 100 <
      FiniteTesting.totalVariation (collapseLaw p (coarseLabels x upperEta))
        (collapseLaw q (coarseLabels x upperEta)) := by
  by_contra hn
  have hc := le_of_not_gt hn
  have hid := totalVariation_collapse_identity p q (coarseLabels x upperEta)
  have hr := allocation_radius_split q x upperEta ε hradius
  have hmin := min_le_right (∑ i ∈ concentratedLabels x upperEta, p.mass i)
    (∑ i ∈ concentratedLabels x upperEta, q.mass i)
  have hE := concentratedResidual_nonneg q x upperEta (fun i => (hx i).2)
  have hO : 0 ≤ localOverlap p q (concentratedLabels x upperEta) :=
    Finset.sum_nonneg (fun i _ => le_min (p.nonneg i) (q.nonneg i))
  dsimp [upperGap] at hc
  dsimp [concentratedLabels] at hr hmin hE hO hD hc
  linarith

theorem finite_allocation_test_of_kkt (q : Probability Ω) (x : Ω → ℝ) (T β ε : ℝ)
    (hT : (1 : ℝ) / 2 ≤ T) (hβ : 0 < β) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hkkt : ∀ i, q.mass i * x i ^ 3 = β * (1 - x i ^ 4) ^ 2)
    (hbudget : 1 = T ^ 2 * β * ∑ i, q.mass i * x i * (1 - x i ^ 4))
    (hradius : (∑ i, q.mass i * x i) = ε)
    (hmax : ∀ i, q.mass i ≤ 2 * (1 - ε)) :
    ∃ (n : ℕ) (test : FiniteTesting.RandomizedTest (Fin n → Ω)),
      (n : ℝ) ≤ (coarseSampleConstant + 10004) * T ∧
      expectation (productLaw q n) test ≤ 1 / 3 ∧
      ∀ p : Probability Ω, ε < FiniteTesting.totalVariation p q →
        1 - expectation (productLaw p n) test ≤ 1 / 3 := by
  have hT0 : 0 ≤ T := by linarith
  have hE0 := concentratedResidual_nonneg q x upperEta (fun i => (hx i).2)
  by_cases hH : (coarseLabels x upperEta).Nonempty
  · obtain ⟨N, coarse, hN, hnull, hcoarse⟩ :=
      exists_allocation_coarse_test q x T β hT hβ hx hkkt hbudget hH
    by_cases hD : coarseDisplacement q x upperEta ≤ 2 * concentratedResidual q x upperEta
    · obtain ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hcoll, hscale⟩ :=
        concentrated_actual_parameters q x T β ε hT hβ hx hkkt hbudget hradius hmax hD
      let m := ⌈10000 * T⌉₊
      let fine := weightedMeanRepeatTest q (concentratedLabels x upperEta) m
      let joined := testMaximum (firstBlockTest N m coarse) (secondBlockTest N m fine)
      have hm0 : 0 < m := by omega
      have hm : (m : ℝ) ≤ 10002 * T := by
        simpa only [m, show (10000 : ℝ) + 2 = 10002 by norm_num] using ceil_scale_le hT (by norm_num : (0 : ℝ) ≤ 10000)
      have hfnull := weightedMeanRepeatTest_null_error q (concentratedLabels x upperEta)
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
        by_cases hc : upperGap q x upperEta / 100 <
            FiniteTesting.totalVariation (collapseLaw p (coarseLabels x upperEta))
              (collapseLaw q (coarseLabels x upperEta))
        · have htest := hcoarse p hc
          have hdom := expectation_le_testMaximum_left (productLaw p (N + m))
            (firstBlockTest N m coarse) (secondBlockTest N m fine)
          rw [expectation_firstBlockTest] at hdom
          change 1 - expectation (productLaw p (N + m)) (testMaximum _ _) ≤ _
          linarith
        · have hO := small_coarse_distance_overlap p q x ε hx hradius hp (le_of_not_gt hc)
          have hf := weightedMeanRepeatTest_alternative_error p q (concentratedLabels x upperEta)
            m w (concentratedResidual q x upperEta) hm2 hw0 hE hA hw hmean hsmall hO hscale
          have hdom := expectation_le_testMaximum_right (productLaw p (N + m))
            (firstBlockTest N m coarse) (secondBlockTest N m fine)
          rw [expectation_secondBlockTest] at hdom
          change 1 - expectation (productLaw p m) fine ≤ 1 / 20 at hf
          change 1 - expectation (productLaw p (N + m)) (testMaximum _ _) ≤ _
          linarith
    · refine ⟨N, coarse, ?_, hnull.trans (by norm_num), ?_⟩
      · have hc : 0 ≤ coarseSampleConstant := by norm_num [coarseSampleConstant]
        nlinarith only [hN, hT0]
      · intro p hp
        exact (hcoarse p (coarse_only_alternative p q x ε hx hradius (lt_of_not_ge hD) hp)).trans (by norm_num)
  · have hH0 := Finset.not_nonempty_iff_eq_empty.mp hH
    have hD0 : coarseDisplacement q x upperEta = 0 := by simp [coarseDisplacement, hH0]
    have hL : concentratedLabels x upperEta = Finset.univ := by simp [concentratedLabels, hH0]
    have hD : coarseDisplacement q x upperEta ≤ 2 * concentratedResidual q x upperEta := by rw [hD0]; linarith
    obtain ⟨hm2, hE, hA, w, hw0, hw, hmean, hsmall, hcoll, hscale⟩ :=
      concentrated_actual_parameters q x T β ε hT hβ hx hkkt hbudget hradius hmax hD
    let m := ⌈10000 * T⌉₊
    have hm0 : 0 < m := by omega
    have hm : (m : ℝ) ≤ 10002 * T := by simpa only [m, show (10000 : ℝ) + 2 = 10002 by norm_num] using ceil_scale_le hT (by norm_num : (0 : ℝ) ≤ 10000)
    refine ⟨m, weightedMeanRepeatTest q (concentratedLabels x upperEta) m, ?_, ?_, ?_⟩
    · have hc : 0 ≤ coarseSampleConstant := by norm_num [coarseSampleConstant]
      have hp := mul_nonneg hc hT0
      nlinarith only [hm, hT0, hp]
    · exact (weightedMeanRepeatTest_null_error q (concentratedLabels x upperEta)
        m w hm0 hA hw hmean hcoll).trans (by norm_num)
    · intro p hp
      have hr := allocation_radius_split q x upperEta ε hradius
      rw [hD0, hL, q.total] at hr
      rw [finite_totalVariation_eq_one_sub_overlap] at hp
      have hO : localOverlap p q (concentratedLabels x upperEta) ≤ 2 * concentratedResidual q x upperEta := by
        rw [hL]
        dsimp [localOverlap]
        linarith
      exact (weightedMeanRepeatTest_alternative_error p q (concentratedLabels x upperEta)
        m w (concentratedResidual q x upperEta) hm2 hw0 hE hA hw hmean hsmall hO hscale).trans (by norm_num)

end IdentityTesting.FiniteAllocationUpper
