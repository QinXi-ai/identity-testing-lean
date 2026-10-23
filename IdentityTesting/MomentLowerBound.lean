import IdentityTesting.FiniteOverlapMoment
import IdentityTesting.FiniteDeletion
import IdentityTesting.GeneralLowerSeparation
import IdentityTesting.SubsetSeedCompression
import IdentityTesting.Endpoints

/-! Original-radius moment lower bound. Deleted mass goes to the new
zero-reference label, so no renormalization or conditioning lemma is needed. -/
noncomputable section
namespace IdentityTesting
open scoped BigOperators
open Classical FiniteTesting EmpiricalSeeds MultiBinSeeds MultiBinExterior SubsetSeedCompression

theorem no_identityTest_of_finite_overlap_moment {k : ℕ}
    (q : Probability (Fin k)) (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : (n : ℝ) * finiteOverlapMoment q δ ≤ (1 : ℝ) / 1000) :
    ¬ HasIdentityTest (extendFiniteLaw q) (1 - δ) n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact no_zero_sample_test (extendFiniteLaw q) (1 - δ) (by linarith)
  let R := momentRetained q δ
  let D := Rᶜ
  let A := liftedDeletionSet R
  let r := padFiniteLaw q
  let ν := deletePaddedLaw q D
  let z := Fin.last k
  have hscale : ∀ y ∈ A, ν.mass y = (1 : ℝ) * r.mass y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hiD : i ∉ D := Finset.notMem_compl.mpr hi
    simp only [ν, r, deletePaddedLaw_mass_castSucc, if_neg hiD,
      padFiniteLaw_mass_castSucc, one_mul]
  have hqA : ∀ y ∈ A, 0 < r.mass y := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa only [r, padFiniteLaw_mass_castSucc] using momentRetained_pos q δ hi
  have hcapA : ∀ y ∈ A, r.mass y ≤ δ / 16 := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    simpa only [r, padFiniteLaw_mass_castSucc] using momentRetained_cap q δ hi
  let ht := subset_scaled_le_one r ν A 1 hscale
  obtain ⟨j, m, hm, hcompress⟩ := exists_uniform_subset_seed_compression r ν A hqA 1
    (by norm_num) hscale (δ / 16) (by positivity) hcapA z
      (last_not_mem_liftedDeletionSet R) 1000 (by norm_num) n (Nat.pos_of_ne_zero hn0)
  let w := subsetCellWeights r A j 1 (by norm_num) ht
  let cells := subsetCellLaws r A hqA j
  let τ := multiBinSeedPrior cells m
  let P : (SeedIndex m → Fin (k + 1)) → Probability (Fin (k + 1)) :=
    multiBinExteriorLaw w (subsetExterior ν A z) m hm
  have hcomp := hcompress ν hscale
  let M := ∑ i ∈ R, (q.mass i) ^ ((3 : ℝ) / 2)
  let W := finiteOverlapMoment q δ
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (q.nonneg i) _)
  have hW : 0 ≤ W := finiteOverlapMoment_nonneg q δ
  have hMbound : M ≤ Real.sqrt δ * W := momentRetained_moment_le q δ hδ
  have hnM : (n : ℝ) * M ≤ Real.sqrt δ / 1000 := by
    calc
      _ ≤ (n : ℝ) * (Real.sqrt δ * W) := mul_le_mul_of_nonneg_left hMbound (Nat.cast_nonneg n)
      _ = Real.sqrt δ * ((n : ℝ) * W) := by ring
      _ ≤ Real.sqrt δ * (1 / 1000) := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg δ)
      _ = _ := by ring
  have hsq : (n : ℝ) ^ 2 * M ^ 2 ≤ δ / 1000000 := by
    have h0 : 0 ≤ (n : ℝ) * M := mul_nonneg (Nat.cast_nonneg n) hM
    have h1 : 0 ≤ Real.sqrt δ / 1000 := by positivity
    have h := (sq_le_sq₀ h0 h1).mpr hnM
    nlinarith only [h, Real.sq_sqrt hδ.le]
  have hO : 2 * 1000 * (n : ℝ) ^ 2 * M ^ 2 + 2 * (δ / 16) < δ := by
    nlinarith only [hsq, hδ]
  have hsumMoment : (∑ y ∈ A, (r.mass y) ^ ((3 : ℝ) / 2)) = M := by
    rw [sum_liftedDeletionSet]
    simp only [r, padFiniteLaw_mass_castSucc, M]
  have hsep (seed : SeedIndex m → Fin (k + 1)) (hs : 0 < τ.mass seed) :
      1 - δ < FiniteTesting.totalVariation (P seed) r := by
    have hout (i : Fin k) (hi : i ∈ D) : (P seed).mass i.castSucc = 0 := by
      have hnR : i ∉ R := Finset.mem_compl.mp hi
      have h := hcomp.2.1 seed hs i.castSucc (by simpa only [A, mem_liftedDeletionSet] using hnR)
      simpa only [ν, deletePaddedLaw_mass_castSucc, if_pos hi] using h
    have hsumZero : (∑ i ∈ D, min ((P seed).mass i.castSucc) (q.mass i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hout i hi, min_eq_left (q.nonneg i)]
    have hsplit := Finset.sum_add_sum_compl R
      (fun i => min ((P seed).mass i.castSucc) (q.mass i))
    change _ + (∑ i ∈ D, min ((P seed).mass i.castSucc) (q.mass i)) = _ at hsplit
    rw [hsumZero, add_zero] at hsplit
    have hover := hcomp.2.2.1 seed hs
    have hsum : (∑ y ∈ A, min ((P seed).mass y) (r.mass y)) =
        ∑ i ∈ R, min ((P seed).mass i.castSucc) (q.mass i) := by
      rw [sum_liftedDeletionSet]
      simp only [r, padFiniteLaw_mass_castSucc]
    rw [hsum, hsumMoment, hsplit] at hover
    rw [GeneralLowerGeometry.padded_totalVariation_eq_one_sub_overlap]
    linarith
  have hdelete : (n : ℝ) * (∑ i ∈ D, q.mass i) ≤ (4 : ℝ) / 1000 := by
    have hmass : (∑ i ∈ D, q.mass i) ≤ 4 * finiteOverlapMoment q δ := by
      apply le_trans ?_ (momentDeleted_mass_le q δ hδ)
      apply le_of_eq
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i
      simp only [D, R, Finset.mem_compl]
    calc
      _ ≤ (n : ℝ) * (4 * finiteOverlapMoment q δ) :=
        mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg n)
      _ = 4 * ((n : ℝ) * finiteOverlapMoment q δ) := by ring
      _ ≤ 4 * (1 / 1000) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  apply no_identityTest_of_padded_prior τ P q (1 - δ) n hsep
  have hdel := deletePaddedLaw_sample_tv_le q D n
  have hseed := hcomp.2.2.2
  have htri := (FiniteTesting.totalVariation_triangle
    (mixture τ (fun seed => productLaw (P seed) n)) (productLaw ν n) (productLaw r n)).trans
      (add_le_add hseed hdel)
  have hbound : (1 : ℝ) ^ 2 / (2 * 1000) + (n : ℝ) * (∑ i ∈ D, q.mass i) < 1 / 3 := by
    linarith only [hdelete]
  exact htri.trans_lt hbound

theorem no_identityTest_of_overlap_moment {k : ℕ}
    (q : Probability (Fin k)) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : (n : ℝ) ≤ (1 : ℝ) / 1000 / overlapMoment (extendFiniteLaw q) δ) :
    ¬ HasIdentityTest (extendFiniteLaw q) (1 - δ) n := by
  apply no_identityTest_of_finite_overlap_moment q δ hδ n
  rw [← overlapMoment_extendFiniteLaw]
  exact (le_div_iff₀ (overlapMoment_pos (extendFiniteLaw q) hδ)).mp hn

end IdentityTesting
