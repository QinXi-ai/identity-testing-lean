import IdentityTesting.HeavyExteriorTilt
import IdentityTesting.HeavyUncompressedPrior
import IdentityTesting.SubsetSeedCompression

/-! # Actual heavy lower prior for radii just above the tail mass -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyLowerGeometry

open Classical FiniteTesting HeavySignedFamily HeavyTilt HeavyExteriorTilt
open EmpiricalSeeds MultiBinSeeds MultiBinExterior SubsetSeedCompression

theorem no_identityTest_of_heavy_boundary_coordinates {k : ℕ}
    (q : Probability (Fin (k + 1))) (x : Fin k → ℝ) (T Δ : ℝ)
    (hT : 0 < T) (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hR0 : 0 < tailTotal q) (hR : tailTotal q ≤ (1 : ℝ) / 4)
    (hbudget : T ^ 2 * (∑ i, (q.mass i.succ) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (hboundary : (∑ i, q.mass i.succ * x i) + Real.sqrt (tailTotal q / T) = tailTotal q)
    (hΔ0 : 0 < Δ) (hΔ : Δ ≤ tailTotal q / 2)
    (n : ℕ) (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 10) * T)
    (hnΔ : (n : ℝ) * Δ ^ 2 / tailTotal q ≤ 1 / (10 : ℝ) ^ 10) :
    ¬ HasIdentityTest (extendFiniteLaw q) (tailTotal q + Δ) n := by
  have hε : tailTotal q + Δ < 2 * tailTotal q := by linarith only [hΔ, hR0]
  by_cases hn0 : n = 0
  · subst n
    exact no_zero_sample_test (extendFiniteLaw q) (tailTotal q + Δ)
      (by linarith only [hR, hΔ])
  have hnpos := Nat.pos_of_ne_zero hn0
  by_cases hTR : T * tailTotal q < (100000000 : ℝ)
  · exact no_identityTest_of_small_heavy_scale_lt_two q hq hR0 hR hTR hε n hn
  have hTR' : (100000000 : ℝ) ≤ T * tailTotal q := le_of_not_gt hTR
  let A := seedSet x
  let g := Real.sqrt (tailTotal q / T)
  let E := highSlack q x
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos hR0 hT)
  have hE : 0 ≤ E := highSlack_nonneg q x (fun i => (hx i).2)
  have hTg := (large_scale_bounds hR0 hT hTR').2.2
  have hgeometry := boundary_geometry q x hx hboundary
  obtain ⟨ν, f, hf1, hf2, htail, hover, hbase⟩ :=
    exists_near_exterior_tilt q hq hR0 hR hT hTR' hΔ0 hΔ
  have hf0 : 0 ≤ f := by linarith only [hf1]
  have hscale : ∀ y ∈ A, ν.mass y = f * q.mass y := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact htail i
  have hqA : ∀ y ∈ A, 0 < q.mass y := fun y _ => hq y
  have hqb : ∀ y ∈ A, q.mass y ≤ 16 / T := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact high_atom_bound q x hq hx hT hbudget i hi
  have hb : 0 ≤ 16 / T := by positivity
  let ht := subset_scaled_le_one q ν A f hscale
  obtain ⟨j, m, hm, hcompress⟩ := exists_uniform_subset_seed_compression q ν A hqA f hf0
    hscale (16 / T) hb hqb 0 (head_not_seedSet x) 1000 (by norm_num) n hnpos
  let w := subsetCellWeights q A j f hf0 ht
  let cells := subsetCellLaws q A hqA j
  let τ := multiBinSeedPrior cells m
  let P : (SeedIndex m → Fin (k + 1)) → Probability (Fin (k + 1)) :=
    fun seed => multiBinExteriorLaw w (subsetExterior ν A 0) m hm seed
  let O := 2 * 1000 * (n : ℝ) ^ 2 * (∑ y ∈ A, (q.mass y) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * (16 / T)
  have hO : O < (E + g) / 100 := by
    have hsum : (∑ y ∈ A, (q.mass y) ^ ((3 : ℝ) / 2)) =
        ∑ i ∈ highTail x, (q.mass i.succ) ^ ((3 : ℝ) / 2) := sum_seedSet x _
    have h := seed_overlap_lt_margin hT hE hg hTg (high_moment_bound q x hx hbudget) n hn
    dsimp only [O]
    rw [hsum]
    convert h using 1; dsimp only [E, g]; ring
  have hcompν : (∑ y ∈ Aᶜ, min (ν.mass y) (q.mass y)) =
      1 - highMass q x - (Δ + 4 * g) := by
    have h := hover Aᶜ (Finset.mem_compl.mpr (head_not_seedSet x))
    rw [complement_seed_mass] at h
    exact h
  apply no_identityTest_extendFiniteLaw_of_finite_prior τ P q (tailTotal q + Δ) n
  · intro seed hs
    have hcompressed := (hcompress ν hscale).2.2.1 seed hs
    have hout := (hcompress ν hscale).2.1 seed hs
    have hcomp : (∑ y ∈ Aᶜ, min ((P seed).mass y) (q.mass y)) =
        1 - highMass q x - (Δ + 4 * g) := by
      rw [← hcompν]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hout y (Finset.mem_compl.mp hy)]
    have hsplit := Finset.sum_add_sum_compl A (fun y => min ((P seed).mass y) (q.mass y))
    rw [hcomp] at hsplit
    rw [finite_totalVariation_eq_one_sub_overlap]
    change (∑ y ∈ A, min ((P seed).mass y) (q.mass y)) ≤ O at hcompressed
    have hlow := hgeometry.1
    have hEbound := hgeometry.2
    change E ≤ g at hEbound
    linarith only [hsplit, hcompressed, hO, hlow, hEbound, hg]
  · have hconditional := (hcompress ν hscale).2.2.2
    have hcost : f ^ 2 / (2 * 1000) + (1 : ℝ) / 10 ^ 4 < 1 / 3 := by
      have hfsq : f ^ 2 ≤ 4 := by nlinarith only [hf1, hf2]
      norm_num
      nlinarith only [hfsq]
    exact ((FiniteTesting.totalVariation_triangle _ (productLaw ν n) _).trans
      (add_le_add hconditional (hbase n hn hnΔ).le)).trans_lt hcost

end IdentityTesting.HeavyLowerGeometry
