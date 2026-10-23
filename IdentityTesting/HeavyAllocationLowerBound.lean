import IdentityTesting.HeavyUncompressedPrior
import IdentityTesting.FinitePriorProduct
import IdentityTesting.SubsetSeedCompression

/-! # Complete actual heavy interior lower bound from allocation coordinates -/

noncomputable section
namespace IdentityTesting.HeavyLowerGeometry
open scoped BigOperators
open Classical
open FiniteTesting HeavySignedFamily HeavyTilt SignedDiagonalMoment
open EmpiricalSeeds MultiBinSeeds MultiBinExterior SubsetSeedCompression

theorem no_identityTest_of_heavy_allocation_coordinates {k : ℕ}
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) (T ε : ℝ)
    (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (hε : (∑ i, q.mass i.succ * x i) + Real.sqrt (tailTotal q / T) = ε)
    (hεR : ε ≤ tailTotal q) (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  by_cases hn0 : n = 0
  · subst n
    exact no_zero_sample_test (extendFiniteLaw q) ε (lt_of_le_of_lt hεR (lt_of_le_of_lt hR (by norm_num)))
  have hnpos := Nat.pos_of_ne_zero hn0
  by_cases hTR : T * tailTotal q < (100000000 : ℝ)
  · exact no_identityTest_of_small_heavy_scale q hq hR0 hR hTR hεR n hn
  have hTR' : (100000000 : ℝ) ≤ T * tailTotal q := le_of_not_gt hTR
  let A := seedSet x
  let g := Real.sqrt (tailTotal q / T)
  let E := highSlack q x
  let margin := (E + g) / 100
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos hR0 hT)
  have hE : 0 ≤ E := highSlack_nonneg q x (fun i => (hx i).2)
  have hTg := (large_scale_bounds hR0 hT hTR').2.2
  have hmoment := high_moment_bound q x hx hbudget
  obtain ⟨ν, f, hf1, hf2, hscale, hlow, hbase⟩ :=
    exists_heavy_uncompressed_prior q x T ε hT hq hx hR0 hR hTR' hbudget hε n hn
  let I := Fin k → Bool
  let ω : Probability I := uniformSigns k
  have hf0 : 0 ≤ f := by linarith only [hf1]
  have hqA : ∀ y ∈ A, 0 < q.mass y := fun y _ => hq y
  have hqb : ∀ y ∈ A, q.mass y ≤ 16 / T := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact high_atom_bound q x hq hx hT hbudget i hi
  have hb : 0 ≤ 16 / T := by positivity
  let σ₀ : I := fun _ => false
  let ht := subset_scaled_le_one q (ν σ₀) A f (hscale σ₀)
  obtain ⟨j, m, hm, hcompress⟩ := exists_uniform_subset_seed_compression q (ν σ₀) A hqA f hf0
    (hscale σ₀) (16 / T) hb hqb 0 (head_not_seedSet x) 1000 (by norm_num) n hnpos
  let w := subsetCellWeights q A j f hf0 ht
  let cells := subsetCellLaws q A hqA j
  let τ := multiBinSeedPrior cells m
  let P : I → (SeedIndex m → Fin (k + 1)) → Probability (Fin (k + 1)) :=
    fun σ seed => multiBinExteriorLaw w (subsetExterior (ν σ) A 0) m hm seed
  let O := 2 * 1000 * (n : ℝ) ^ 2 * (∑ y ∈ A, (q.mass y) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * (16 / T)
  have hO : O < margin := by
    have hsum : (∑ y ∈ A, (q.mass y) ^ ((3 : ℝ) / 2)) =
        ∑ i ∈ highTail x, (q.mass i.succ) ^ ((3 : ℝ) / 2) := sum_seedSet x _
    have h := seed_overlap_lt_margin hT hE hg hTg hmoment n hn
    dsimp only [O, margin]
    rw [hsum]
    convert h using 1; dsimp only [E, g]; ring
  have hsep (σ : I) (seed : SeedIndex m → Fin (k + 1)) (hs : 0 < τ.mass seed) :
      ε < FiniteTesting.totalVariation (P σ seed) q := by
    have hover := (hcompress (ν σ) (hscale σ)).2.2.1 seed hs
    have hout := (hcompress (ν σ) (hscale σ)).2.1 seed hs
    have hcomp : (∑ y ∈ Aᶜ, min ((P σ seed).mass y) (q.mass y)) =
        ∑ y ∈ Aᶜ, min ((ν σ).mass y) (q.mass y) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hout y (Finset.mem_compl.mp hy)]
    have hsplit := Finset.sum_add_sum_compl A (fun y => min ((P σ seed).mass y) (q.mass y))
    have hlowσ := hlow σ
    change _ ≤ 1 - ε - margin at hlowσ
    rw [hcomp] at hsplit
    rw [finite_totalVariation_eq_one_sub_overlap]
    change (∑ y ∈ A, min ((P σ seed).mass y) (q.mass y)) ≤ O at hover
    linarith only [hover, hsplit, hlowσ, hO]
  let η := f ^ 2 / (2 * 1000)
  have hconditional (σ : I) :
      FiniteTesting.totalVariation (mixture τ (fun seed => productLaw (P σ seed) n))
        (productLaw (ν σ) n) ≤ η :=
    (hcompress (ν σ) (hscale σ)).2.2.2
  have hcost : η + (1 : ℝ) / 10 ^ 3 < 1 / 3 := by
    have hfsq : f ^ 2 ≤ 4 := by nlinarith only [hf1, hf2]
    have hfrac := div_le_div_of_nonneg_right hfsq (by norm_num : (0 : ℝ) ≤ 2 * 1000)
    dsimp only [η]
    norm_num at hfrac ⊢
    linarith only [hfrac]
  apply no_identityTest_extendFiniteLaw_of_finite_prior (productPrior ω τ) (fun ij => P ij.1 ij.2) q ε n
  · intro ij hij
    exact hsep ij.1 ij.2 ((productPrior_mass_pos_iff ω τ ij.1 ij.2).mp hij).2
  · exact (two_stage_sample_tv_le ω τ P ν q n η ((1 : ℝ) / 10 ^ 3)
      (fun σ _ => hconditional σ) hbase.le).trans_lt hcost

end IdentityTesting.HeavyLowerGeometry
