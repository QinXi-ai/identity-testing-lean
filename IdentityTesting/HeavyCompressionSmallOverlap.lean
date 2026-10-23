import IdentityTesting.HeavyCompressionPrior
import IdentityTesting.HeavySmallScaleBounds

/-! The exact small-overlap estimate for the constructed feasible heavy seed prior. -/
noncomputable section
namespace IdentityTesting.HeavyCompressionFeasible
open scoped BigOperators
open Classical FiniteTesting HeavySignedFamily HeavyLowerGeometry SubsetSeedCompression
open EmpiricalSeeds MultiBinSeeds MultiBinExterior SeedExterior

theorem compression_small_overlap_scalar {T E A b g : ℝ}
    (hT : 0 < T) (hE : 0 ≤ E) (hg : 0 < g) (hTg : 10000 ≤ T * g)
    (hbudget : T ^ 2 * A ^ 2 ≤ 1024 * E) (hb : b < 16 / T)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    2 * 1000 * (n : ℝ) ^ 2 * A ^ 2 + 2 * b ≤
      2048 * 1000 * (1 / (10 : ℝ) ^ 10) ^ 2 * E + 32 / T ∧
    2048 * 1000 * (1 / (10 : ℝ) ^ 10) ^ 2 * E + 32 / T < (E + g) / 100 := by
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  have hs := mul_le_mul_of_nonneg_right hn2 (sq_nonneg A)
  have hbgt := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ (1 / (10 : ℝ) ^ 10) ^ 2)
  have hrem : 32 / T ≤ 32 / 10000 * g := by
    apply (div_le_iff₀ hT).2
    nlinarith only [hTg]
  constructor
  · have hsq : (n : ℝ) ^ 2 * A ^ 2 ≤ (1 / (10 : ℝ) ^ 10) ^ 2 * (1024 * E) := by
      calc
        _ ≤ (1 / (10 : ℝ) ^ 10 * T) ^ 2 * A ^ 2 := hs
        _ = (1 / (10 : ℝ) ^ 10) ^ 2 * (T ^ 2 * A ^ 2) := by ring
        _ ≤ _ := hbgt
    have hb2 : 2 * b ≤ 32 / T := by
      calc
        _ ≤ 2 * (16 / T) := mul_le_mul_of_nonneg_left hb.le (by norm_num)
        _ = _ := by ring
    convert add_le_add (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2000)) hb2 using 1 <;> ring
  · nlinarith only [hrem, hE, hg]

theorem exists_feasible_small_overlap_prior {k : ℕ}
    (q ν : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    {T : ℝ} (hT : 0 < T) (hR : 0 < tailTotal q)
    (hTR : 100000000 ≤ T * tailTotal q)
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤ 1)
    (f : ℝ) (hf1 : 1 ≤ f) (hf2 : f ≤ 2)
    (hscale : ∀ i ∈ seedSet x, ν.mass i = f * q.mass i)
    (n : ℕ) (hn0 : 0 < n) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ∃ (I : Type) (_ : Fintype I) (ω : Probability I) (P : I → Probability (Fin (k + 1))),
      (∀ seed, 0 < ω.mass seed →
        (∀ i, i ∉ seedSet x → (P seed).mass i = ν.mass i) ∧
        (∑ i ∈ seedSet x, min ((P seed).mass i) (q.mass i)) <
          (highSlack q x + Real.sqrt (tailTotal q / T)) / 100) ∧
      FiniteTesting.totalVariation (mixture ω (fun seed => productLaw (P seed) n))
        (productLaw ν n) ≤ f ^ 2 / 2000 := by
  obtain ⟨_, hmoment, hmax, j, m, hm, hseed, htv⟩ :=
    exists_feasible_compression_prior q ν x hq hx hT hbudget f hf1 hf2 hscale
      1000 (by norm_num) n hn0
  obtain ⟨hg, _, hTg⟩ := large_scale_bounds hR hT hTR
  have hsmall := compression_small_overlap_scalar hT (highSlack_nonneg q x (fun i => (hx i).2))
    hg hTg hmoment hmax n hn
  let cells := subsetCellLaws q (seedSet x) (fun i (_ : i ∈ seedSet x) => hq i) j
  let w := subsetCellWeights q (seedSet x) j f (by linarith : 0 ≤ f)
    (subset_scaled_le_one q ν (seedSet x) f hscale)
  refine ⟨SeedIndex m → Fin (k + 1), inferInstance, multiBinSeedPrior cells m,
    (fun seed => multiBinExteriorLaw w (subsetExterior ν (seedSet x) 0) m hm seed), ?_, ?_⟩
  · intro seed hs
    obtain ⟨hout, hover⟩ := hseed seed hs
    exact ⟨hout, hover.trans_lt (hsmall.1.trans_lt hsmall.2)⟩
  · simpa only [show (2 : ℝ) * 1000 = 2000 by norm_num] using htv

end IdentityTesting.HeavyCompressionFeasible
