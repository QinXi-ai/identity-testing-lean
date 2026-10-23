import IdentityTesting.HeavySignedMoment

/-! # The actual heavy signed prior's IID sample bound -/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.HeavySignedLowerBound

open HeavySignedFamily HeavySignedBudget HeavySignedMoment SignedDiagonalMoment

variable {k : ℕ}

theorem heavyLaw_iid_pair_moment_le
    (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hq : ∀ i, 0 < q.mass i) (n : ℕ)
    (hsmall : (n : ℝ) ^ 2 * diagonalEnergy q a ≤ 1 / 4) :
    (∑ σ : Fin k → Bool, ∑ τ : Fin k → Bool,
      (uniformSigns k).mass σ * (uniformSigns k).mass τ *
        (FiniteChiSquare.likelihoodInner (heavyLaw q a ha hR σ) (heavyLaw q a ha hR τ) q) ^ n) ≤
          Real.exp (2 * (n : ℝ) ^ 2 * diagonalEnergy q a) := by
  apply le_trans _ (structured_pairExp_le (fun i => a i ^ 2 / q.mass i.succ) a
    (hq 0) rfl (rankVariance_head_bound q a hq hR) hsmall)
  unfold pairExp
  apply Finset.sum_le_sum
  intro σ _
  apply Finset.sum_le_sum
  intro τ _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg ((uniformSigns k).nonneg σ) ((uniformSigns k).nonneg τ))
  let I : ℝ := diagonalInteraction (fun i => a i ^ 2 / q.mass i.succ) σ τ +
    signedSum a σ * signedSum a τ / q.mass 0
  have hinner : FiniteChiSquare.likelihoodInner (heavyLaw q a ha hR σ) (heavyLaw q a ha hR τ) q =
      1 + I := by rw [heavyLaw_likelihoodInner q a ha hR hq]; dsimp [I]; ring
  have hnonneg := likelihoodInner_nonneg (heavyLaw q a ha hR σ) (heavyLaw q a ha hR τ) q
  rw [hinner] at hnonneg ⊢
  have hbase : 1 + I ≤ Real.exp I := by linarith only [Real.add_one_le_exp I]
  have hp := pow_le_pow_left₀ hnonneg hbase n
  exact hp.trans_eq (Real.exp_nat_mul I n).symm

theorem heavyLaw_iid_chiSquare_le
    (q : FiniteTesting.Probability (Fin (k + 1))) (a : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ q.mass i.succ) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hq : ∀ i, 0 < q.mass i) (n : ℕ)
    (hsmall : (n : ℝ) ^ 2 * diagonalEnergy q a ≤ 1 / 4) :
    FiniteChiSquare.chiSquare
      (FiniteTesting.mixture (uniformSigns k) (fun σ => FiniteTesting.productLaw (heavyLaw q a ha hR σ) n))
      (FiniteTesting.productLaw q n) ≤ Real.exp (2 * (n : ℝ) ^ 2 * diagonalEnergy q a) - 1 := by
  have hm := heavyLaw_iid_pair_moment_le q a ha hR hq n hsmall
  have hi := FiniteChiSquare.one_add_chiSquare_iid_mixture (uniformSigns k) (heavyLaw q a ha hR) q n
  linarith only [hm, hi]

def allocationHeavyLaw (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hR : tailTotal q ≤ (1 : ℝ) / 4) (σ : Fin k → Bool) :
    FiniteTesting.Probability (Fin (k + 1)) :=
  heavyLaw q (allocationAmplitude q x) (allocationAmplitude_bounds q x hx) hR σ

theorem allocationHeavyLaw_mass_outside
    (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (σ : Fin k → Bool) (i : Fin k) (hi : (1 : ℝ) / 4 < x i) :
    (allocationHeavyLaw q x hx hR σ).mass i.succ = q.mass i.succ := by
  simp only [allocationHeavyLaw, heavyLaw_mass_tail, allocationAmplitude, if_neg (not_le.mpr hi),
    zero_mul, add_zero]

theorem allocationHeavyLaw_head_selected_total
    (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hR : tailTotal q ≤ (1 : ℝ) / 4) (σ : Fin k → Bool) :
    (allocationHeavyLaw q x hx hR σ).mass 0 +
        (∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4),
          (allocationHeavyLaw q x hx hR σ).mass i.succ) =
      q.mass 0 + ∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4), q.mass i.succ := by
  have hsign : signedSum (allocationAmplitude q x) σ =
      ∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4),
        allocationAmplitude q x i * sign (σ i) := by
    unfold signedSum
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x i ≤ (1 : ℝ) / 4
    · simp only [hi, if_true]
    · simp only [hi, if_false, allocationAmplitude, zero_mul]
  simp only [allocationHeavyLaw, heavyLaw_mass_head, heavyLaw_mass_tail, Finset.sum_add_distrib]
  linarith only [hsign]

theorem allocationHeavyLaw_totalVariation_ge
    (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hR : tailTotal q ≤ (1 : ℝ) / 4) (σ : Fin k → Bool) :
    2 * (∑ i ∈ Finset.univ.filter (fun i => x i ≤ (1 : ℝ) / 4), q.mass i.succ * x i) ≤
      FiniteTesting.totalVariation (allocationHeavyLaw q x hx hR σ) q := by
  have h := heavyLaw_totalVariation_ge q (allocationAmplitude q x)
    (allocationAmplitude_bounds q x hx) hR σ
  rw [allocationAmplitude_sum] at h
  dsimp [allocationHeavyLaw]
  linarith only [h]

theorem allocationHeavyLaw_sample_totalVariation_lt
    (q : FiniteTesting.Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR : tailTotal q ≤ (1 : ℝ) / 4) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    FiniteTesting.totalVariation
      (FiniteTesting.mixture (uniformSigns k)
        (fun σ => FiniteTesting.productLaw (allocationHeavyLaw q x (fun i => (hx i).1) hR σ) n))
      (FiniteTesting.productLaw q n) < 1 / (10 : ℝ) ^ 6 := by
  let a := allocationAmplitude q x
  let D := diagonalEnergy q a
  have hD : D ≤ 256 / T ^ 2 := allocation_diagonalEnergy_bound q x hq hx hT hbudget
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  have hnD : (n : ℝ) ^ 2 * D ≤ 256 / (10 : ℝ) ^ 20 := by
    calc
      _ ≤ (n : ℝ) ^ 2 * (256 / T ^ 2) := mul_le_mul_of_nonneg_left hD (sq_nonneg _)
      _ = 256 * (n : ℝ) ^ 2 / T ^ 2 := by ring
      _ ≤ _ := by
        apply (div_le_iff₀ (sq_pos_of_pos hT)).2
        norm_num at hn2 ⊢
        nlinarith only [hn2]
  have hsmall : (n : ℝ) ^ 2 * D ≤ 1 / 4 := by norm_num at hnD ⊢; linarith only [hnD]
  have hchi := heavyLaw_iid_chiSquare_le q a (allocationAmplitude_bounds q x (fun i => (hx i).1))
    hR hq n hsmall
  have hz : 2 * (n : ℝ) ^ 2 * D ≤ 512 / (10 : ℝ) ^ 20 := by nlinarith only [hnD]
  have hexp := (Real.exp_le_exp.mpr hz).trans (Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 512 / (10 : ℝ) ^ 20) (by norm_num))
  let Q := FiniteTesting.mixture (uniformSigns k)
    (fun σ => FiniteTesting.productLaw (allocationHeavyLaw q x (fun i => (hx i).1) hR σ) n)
  let qn := FiniteTesting.productLaw q n
  have hchiSmall : FiniteChiSquare.chiSquare Q qn < 4 / (10 : ℝ) ^ 12 := by
    have hnum : (1 : ℝ) / (1 - 512 / (10 : ℝ) ^ 20) - 1 < 4 / (10 : ℝ) ^ 12 := by norm_num
    change FiniteChiSquare.chiSquare Q qn ≤ Real.exp (2 * (n : ℝ) ^ 2 * D) - 1 at hchi
    linarith only [hchi, hexp, hnum]
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four Q qn
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  change FiniteTesting.totalVariation Q qn < 1 / (10 : ℝ) ^ 6
  by_contra hnot
  have hlarge : 1 / (10 : ℝ) ^ 6 ≤ FiniteTesting.totalVariation Q qn := le_of_not_gt hnot
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 6) hlarge
  norm_num at hchiSmall hsq
  nlinarith only [hchiSmall, hTV, hsq]

end IdentityTesting.HeavySignedLowerBound
