import IdentityTesting.GeneralUncompressedPrior
import IdentityTesting.FiniteDeletion
import IdentityTesting.FinitePriorProduct
import IdentityTesting.SubsetSeedCompression

/-! Assembly of actual all-radius allocation priors for finite non-heavy references. -/

noncomputable section
namespace IdentityTesting.GeneralLowerGeometry
open scoped BigOperators
open Classical
open FiniteTesting SortedPairing SignedDiagonalMoment EmpiricalSeeds
open MultiBinSeeds MultiBinExterior SubsetSeedCompression

theorem no_identityTest_of_general_allocation_coordinates {k : ℕ}
    (q : Probability (Fin k)) (x : Fin k → ℝ) (T ε : ℝ)
    (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (hcap : ∀ i, q.mass i ≤ (4 : ℝ) / 5)
    (hgeom : ∀ i j, q.mass i ≤ q.mass j → q.mass i * x i ≤ q.mass j * x j)
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (hε : (∑ i, q.mass i * x i) = ε)
    (n : ℕ) (hn0 : 0 < n) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  have hk : k ≠ 0 := by
    intro hk
    subst k
    have ht := q.total
    simp at ht
  letI : NeZero k := ⟨hk⟩
  let H := lowCoords x
  let S := highCoords x
  let L := separationMargin q.mass x
  let D := deletedCoords S q.mass L
  let R := retainedCoords S q.mass L
  let A := liftedDeletionSet R
  let r := padFiniteLaw q
  let z := Fin.last k
  have hL : 0 < L := separationMargin_pos q.mass x hq hx
  have hD : D ⊆ S := Finset.filter_subset _ _
  have hR : R ⊆ S := Finset.sdiff_subset
  have hRD (i : Fin k) (hi : i ∈ R) : i ∉ D := (Finset.mem_sdiff.mp hi).2
  have hDR (i : Fin k) (hi : i ∈ D) : i ∉ R := by
    intro hir
    exact hRD i hir hi
  have hHS (i : Fin k) (hi : i ∈ H) : i ∉ S := by
    exact Finset.notMem_compl.mpr hi
  have hmassmoment : T ^ 2 * (∑ i ∈ S, (q.mass i) ^ ((3 : ℝ) / 2)) ^ 2 ≤ 16384 * L :=
    high_moment_le_margin q.mass x T q.nonneg (fun i => ⟨(hx i).1.le, (hx i).2⟩) hbudget
  have hn' : (n : ℝ) ≤ T / 1000000000000 := by
    convert hn using 1 <;> norm_num <;> ring
  have hdelete : (n : ℝ) * (∑ i ∈ D, q.mass i) ≤ (128000 : ℝ) / 1000000000000 :=
    deleted_sample_cost S q.mass T L q.nonneg hT hL hmassmoment n hn'
  obtain ⟨ν, f, hf1, hf3, hνhigh, hνlow, hνTV⟩ :=
    exists_general_uncompressed_prior q x T hT hq (fun i => ⟨(hx i).1.le, (hx i).2⟩)
      hcap hgeom hbudget n hn
  let I := Fin (pairCount q.mass H) → Bool
  let ω : Probability I := uniformSigns (pairCount q.mass H)
  let νd : I → Probability (Fin (k + 1)) := fun σ => deletePaddedLaw (ν σ) D
  have hf0 : 0 ≤ f := by linarith
  have hscale (σ : I) : ∀ y ∈ A, (νd σ).mass y = f * r.mass y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    rw [deletePaddedLaw_mass_castSucc, if_neg (hRD i hi), padFiniteLaw_mass_castSucc]
    exact hνhigh σ i (hR hi)
  have hqA : ∀ y ∈ A, 0 < r.mass y := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    simpa only [r, padFiniteLaw_mass_castSucc] using hq i
  have hqbA : ∀ y ∈ A, r.mass y ≤ L / 1000000 := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa only [r, padFiniteLaw_mass_castSucc] using retainedCoords_mass_le S q.mass L i hi
  have hz : z ∉ A := last_not_mem_liftedDeletionSet R
  have hb : 0 ≤ L / 1000000 := by positivity
  let σ₀ : I := fun _ => false
  let ht := subset_scaled_le_one r (νd σ₀) A f (hscale σ₀)
  obtain ⟨j, m, hm, hcompress⟩ := exists_uniform_subset_seed_compression r (νd σ₀) A hqA f hf0
    (hscale σ₀) (L / 1000000) hb hqbA z hz 100000 (by norm_num) n hn0
  let w := subsetCellWeights r A j f hf0 ht
  let cells := subsetCellLaws r A hqA j
  let τ := multiBinSeedPrior cells m
  let P : I → (SeedIndex m → Fin (k + 1)) → Probability (Fin (k + 1)) :=
    fun σ seed => multiBinExteriorLaw w (subsetExterior (νd σ) A z) m hm seed
  let O := 2 * 100000 * (n : ℝ) ^ 2 * (∑ y ∈ A, (r.mass y) ^ ((3 : ℝ) / 2)) ^ 2 +
    2 * (L / 1000000)
  have hO : O < L := by
    have hsum : (∑ y ∈ A, (r.mass y) ^ ((3 : ℝ) / 2)) =
        ∑ i ∈ R, (q.mass i) ^ ((3 : ℝ) / 2) := by
      rw [sum_liftedDeletionSet]
      simp only [r, padFiniteLaw_mass_castSucc]
    have hle : (∑ i ∈ R, (q.mass i) ^ ((3 : ℝ) / 2)) ≤
        ∑ i ∈ S, (q.mass i) ^ ((3 : ℝ) / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hR (fun i _ _ => Real.rpow_nonneg (q.nonneg i) _)
    have hs1 : 0 ≤ ∑ i ∈ R, (q.mass i) ^ ((3 : ℝ) / 2) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)
    have hs2 : 0 ≤ ∑ i ∈ S, (q.mass i) ^ ((3 : ℝ) / 2) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)
    have hMR := (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hs1 hs2).mpr hle) (sq_nonneg T)).trans hmassmoment
    have hbnd := seed_overlap_lt_margin_fraction
      (∑ i ∈ R, (q.mass i) ^ ((3 : ℝ) / 2)) T L hT hL hMR n hn'
    dsimp only [O]
    rw [hsum]
    exact hbnd.trans (by linarith)
  have hout (σ : I) (seed : SeedIndex m → Fin (k + 1)) (hs : 0 < τ.mass seed)
      (i : Fin k) (hi : i ∉ R) : (P σ seed).mass i.castSucc = (νd σ).mass i.castSucc := by
    exact (hcompress (νd σ) (hscale σ)).2.1 seed hs i.castSucc
      (by simpa only [A, mem_liftedDeletionSet] using hi)
  have hsep (σ : I) (seed : SeedIndex m → Fin (k + 1)) (hs : 0 < τ.mass seed) :
      ε < FiniteTesting.totalVariation (P σ seed) r := by
    apply compressed_alternative_separated q x ε O hε (P σ seed) ?_ ?_ hO
    · calc
        _ = ∑ i ∈ H, min ((ν σ).mass i) (q.mass i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hout σ seed hs i (fun hir => hHS i hi (hR hir)),
            deletePaddedLaw_mass_castSucc, if_neg (fun hid => hHS i hi (hD hid))]
        _ ≤ _ := hνlow σ
    · have hzero : (∑ i ∈ D, min ((P σ seed).mass i.castSucc) (q.mass i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hout σ seed hs i (hDR i hi), deletePaddedLaw_mass_castSucc, if_pos hi,
          min_eq_left (q.nonneg i)]
      have hsplit := Finset.sum_sdiff (f := fun i => min ((P σ seed).mass i.castSucc) (q.mass i)) hD
      rw [hzero, add_zero] at hsplit
      have hover := (hcompress (νd σ) (hscale σ)).2.2.1 seed hs
      have hsum : (∑ y ∈ A, min ((P σ seed).mass y) (r.mass y)) =
          ∑ i ∈ R, min ((P σ seed).mass i.castSucc) (q.mass i) := by
        rw [sum_liftedDeletionSet]
        simp only [r, padFiniteLaw_mass_castSucc]
      rw [hsum] at hover
      change (∑ i ∈ S, min ((P σ seed).mass i.castSucc) (q.mass i)) ≤ O
      rw [← hsplit]
      exact hover
  let η := f ^ 2 / (2 * 100000) + (n : ℝ) * f * ∑ i ∈ D, q.mass i
  have hconditional (σ : I) :
      FiniteTesting.totalVariation (mixture τ (fun seed => productLaw (P σ seed) n))
        (productLaw (padFiniteLaw (ν σ)) n) ≤ η := by
    have hseed := (hcompress (νd σ) (hscale σ)).2.2.2
    have hdel := deletePaddedLaw_sample_tv_le (ν σ) D n
    have hsum : (∑ i ∈ D, (ν σ).mass i) = f * ∑ i ∈ D, q.mass i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hνhigh σ i (hD hi))
    rw [hsum] at hdel
    have htri := (FiniteTesting.totalVariation_triangle
      (mixture τ (fun seed => productLaw (P σ seed) n))
      (productLaw (νd σ) n) (productLaw (padFiniteLaw (ν σ)) n)).trans (add_le_add hseed hdel)
    convert htri using 1 <;> dsimp only [η] <;> ring
  have hbase : FiniteTesting.totalVariation
      (mixture ω (fun σ => productLaw (padFiniteLaw (ν σ)) n)) (productLaw r n) ≤
        (1 : ℝ) / 10 ^ 5 :=
    (padded_sample_mixture_tv_le ω ν q n).trans hνTV.le
  have hcost : η + (1 : ℝ) / 10 ^ 5 < 1 / 3 := by
    have hd : 0 ≤ (n : ℝ) * ∑ i ∈ D, q.mass i :=
      mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg (fun i _ => q.nonneg i))
    have hscaled := mul_le_mul_of_nonneg_right hf3 hd
    have hsmall := mul_le_mul_of_nonneg_left hdelete (by norm_num : (0 : ℝ) ≤ 3)
    have hfsq : f ^ 2 ≤ 9 := by nlinarith only [hf1, hf3]
    have hfrac := div_le_div_of_nonneg_right hfsq (by norm_num : (0 : ℝ) ≤ 2 * 100000)
    dsimp only [η]
    nlinarith only [hscaled, hsmall, hfrac, tilted_combined_cost_lt]
  apply no_identityTest_of_padded_prior (productPrior ω τ) (fun ij => P ij.1 ij.2) q ε n
  · intro ij hij
    exact hsep ij.1 ij.2 ((productPrior_mass_pos_iff ω τ ij.1 ij.2).mp hij).2
  · exact (two_stage_sample_tv_le ω τ P (fun σ => padFiniteLaw (ν σ)) r n η
      ((1 : ℝ) / 10 ^ 5) (fun σ _ => hconditional σ) hbase).trans_lt hcost

/-- The allocation coordinates and their ordering come from the actual optimizer
at the original countable allocation root. No prior or separation certificate is
an input to this finite non-heavy lower bound. -/
theorem no_identityTest_of_general_allocation_root {k : ℕ}
    (q : Probability (Fin k)) (hq : ∀ i, 0 < q.mass i)
    (hcap : ∀ i, q.mass i ≤ (4 : ℝ) / 5)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) *
      allocationRoot (extendFiniteLaw q) ε) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  by_cases hn0 : n = 0
  · subst n
    exact no_zero_sample_test (extendFiniteLaw q) ε hε1
  obtain ⟨hT, x, β, hx, hsum, hbudget, hβ, hstationary, _⟩ :=
    exists_finite_allocation_coordinates_at_root q hq hε0 hε1
  apply no_identityTest_of_general_allocation_coordinates q x
    (allocationRoot (extendFiniteLaw q) ε) ε hT hq hx hcap ?_ hbudget hsum n
      (Nat.pos_of_ne_zero hn0) hn
  intro i j hij
  exact (allocation_stationary_geometry (hq j) hβ (hx i).1 (hx i).2
    (hx j).1 (hx j).2 hij (hstationary i) (hstationary j)).2

end IdentityTesting.GeneralLowerGeometry
