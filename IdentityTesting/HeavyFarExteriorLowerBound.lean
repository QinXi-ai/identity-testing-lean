import IdentityTesting.HeavyTilt
import IdentityTesting.FinitePadding

/-! # Zero-label contamination for the far exterior heavy range -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyFarExterior

open Classical FiniteTesting EmpiricalSeeds HeavySignedFamily

variable {Ω : Type*} [Fintype Ω]

def contaminationLaw (q : Probability Ω) (j : Ω) (z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : Probability Ω where
  mass i := (1 - z) * q.mass i + z * (pointLaw j).mass i
  nonneg i := add_nonneg (mul_nonneg (sub_nonneg.mpr hz1) (q.nonneg i))
    (mul_nonneg hz0 ((pointLaw j).nonneg i))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, q.total, (pointLaw j).total]
    ring

theorem contaminationLaw_totalVariation (q : Probability Ω) (j : Ω) (hqj : q.mass j = 0)
    (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    FiniteTesting.totalVariation (contaminationLaw q j z hz0 hz1) q = z := by
  have hmin (i : Ω) : min ((contaminationLaw q j z hz0 hz1).mass i) (q.mass i) =
      (1 - z) * q.mass i := by
    by_cases hij : i = j
    · subst i
      simp only [contaminationLaw, pointLaw_mass, hqj, ite_true, mul_zero, mul_one, zero_add]
      exact min_eq_right hz0
    · simp only [contaminationLaw, pointLaw_mass, if_neg hij, mul_zero, add_zero]
      apply min_eq_left
      have h := mul_nonneg hz0 (q.nonneg i)
      nlinarith only [h]
  rw [finite_totalVariation_eq_one_sub_overlap]
  simp_rw [hmin]
  rw [← Finset.mul_sum, q.total]
  ring

theorem contaminationLaw_sample_totalVariation_le
    (q : Probability Ω) (j : Ω) (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    FiniteTesting.totalVariation (productLaw (contaminationLaw q j z hz0 hz1) n)
      (productLaw q n) ≤ (n : ℝ) * z := by
  let r := (1 - z) ^ n
  have hr0 : 0 ≤ r := pow_nonneg (sub_nonneg.mpr hz1) n
  have hr1 : r ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hz1) (by linarith only [hz0])
  have hprod (sample : Fin n → Ω) : r * (productLaw q n).mass sample ≤
      (productLaw (contaminationLaw q j z hz0 hz1) n).mass sample := by
    have h : (∏ i : Fin n, (1 - z) * q.mass (sample i)) ≤
        ∏ i : Fin n, (contaminationLaw q j z hz0 hz1).mass (sample i) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (sub_nonneg.mpr hz1) (q.nonneg _)
      · intro i _
        exact le_add_of_nonneg_right (mul_nonneg hz0 ((pointLaw j).nonneg _))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, productLaw_mass, r] using h
  have hover : r ≤ ∑ sample, min ((productLaw (contaminationLaw q j z hz0 hz1) n).mass sample)
      ((productLaw q n).mass sample) := by
    calc
      r = ∑ sample, r * (productLaw q n).mass sample := by
        rw [← Finset.mul_sum, (productLaw q n).total, mul_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro sample _
        exact le_min (hprod sample)
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 ((productLaw q n).nonneg sample))
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -z by linarith only [hz1]) n
  rw [finite_totalVariation_eq_one_sub_overlap]
  change 1 - _ ≤ _
  change 1 + (n : ℝ) * -z ≤ (1 + -z) ^ n at hbern
  dsimp only [r] at hover
  have hpow : 1 - (n : ℝ) * z ≤ (1 - z) ^ n := by
    convert hbern using 1; ring
  linarith only [hover, hpow]

theorem no_identityTest_of_far_exterior {k : ℕ}
    (q : Probability (Fin (k + 1))) {Δ : ℝ}
    (hR0 : 0 < tailTotal q) (hΔ : tailTotal q / 2 ≤ Δ)
    (hε : tailTotal q + Δ < 1) (n : ℕ) (hn : (n : ℝ) ≤ 1 / (36 * Δ)) :
    ¬ HasIdentityTest (extendFiniteLaw q) (tailTotal q + Δ) n := by
  let ε := tailTotal q + Δ
  have hΔ0 : 0 < Δ := by linarith only [hR0, hΔ]
  have hε0 : 0 < ε := by dsimp only [ε]; linarith only [hR0, hΔ0]
  let z := min (2 * ε) ((1 + ε) / 2)
  have hεz : ε < z := lt_min (by linarith only [hε0]) (by change ε < 1 at hε; linarith only [hε])
  have hz0 : 0 ≤ z := hε0.le.trans hεz.le
  have hz1 : z ≤ 1 := (min_le_right _ _).trans (by change ε < 1 at hε; linarith only [hε])
  have hzΔ : z ≤ 6 * Δ := by
    have h := min_le_left (2 * ε) ((1 + ε) / 2)
    dsimp only [ε] at h
    linarith only [h, hΔ]
  let q' := padFiniteLaw q
  let p := contaminationLaw q' (Fin.last (k + 1)) z hz0 hz1
  have hpsep : tailTotal q + Δ < FiniteTesting.totalVariation p q' := by
    rw [contaminationLaw_totalVariation q' _ (padFiniteLaw_mass_last q)]
    exact hεz
  have hnΔ : (n : ℝ) * Δ ≤ 1 / 36 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 36) hΔ0)).mp hn
    linarith only [h]
  have htv : FiniteTesting.totalVariation (productLaw p n) (productLaw q' n) < (1 : ℝ) / 3 := by
    have h := contaminationLaw_sample_totalVariation_le q' (Fin.last (k + 1)) z hz0 hz1 n
    have hnz := mul_le_mul_of_nonneg_left hzΔ (Nat.cast_nonneg n)
    linarith only [h, hnz, hnΔ]
  apply no_identityTest_of_padded_prior (pointLaw ()) (fun _ : Unit => p) q (tailTotal q + Δ) n
  · intro _ _
    exact hpsep
  · simpa only [mixture_constant] using htv

end IdentityTesting.HeavyFarExterior
