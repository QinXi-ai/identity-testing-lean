import IdentityTesting.SubsetSeedDecomposition
import IdentityTesting.DyadicExterior

/-! Actual dyadic compression of a specified subset. The chosen cells, counts,
seed prior, and sample kernel are shared by all laws with the same masses on
the subset. Empty subsets and zero exterior mass are included. -/

noncomputable section
namespace IdentityTesting.SubsetSeedCompression
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds MultiBinSeeds MultiBinExterior SeedExterior

universe u
variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]

theorem subsetOverlap_eq (r q : Probability Ω) (S : Finset Ω) :
    (∑ x, min (r.mass x) (if x ∈ S then q.mass x else 0)) =
      ∑ x ∈ S, min (r.mass x) (q.mass x) := by
  calc
    _ = ∑ x, if x ∈ S then min (r.mass x) (q.mass x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · simp only [if_pos hx]
      · simp only [if_neg hx, min_eq_right (r.nonneg x)]
    _ = _ := by simp

omit [DecidableEq Ω] in
/-- Parent dyadic allocation, extended to the genuinely empty subset. -/
theorem exists_subset_dyadic_counts (q : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (b : ℝ) (hb : 0 ≤ b)
    (hqb : ∀ x ∈ S, q.mass x ≤ b) (B : ℝ) (hB : 0 < B)
    (n : ℕ) (hn : 0 < n) :
    ∃ (j : S → ℕ) (m : OccupiedCells j → ℕ),
      (∀ i : S, subsetAtoms q S i ≤ dyadicUpper b (j i)) ∧
      (∀ l, 0 < m l) ∧
      (∑ l, (m l : ℝ) * dyadicUpper b l.val) ≤
        2 * B * (n : ℝ) ^ 2 * (∑ x ∈ S, (q.mass x) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b ∧
      (n.choose 2 : ℝ) * (∑ l, (cellMass (subsetAtoms q S) j l) ^ 2 / (m l : ℝ)) ≤
        1 / (2 * B) := by
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    letI : Nonempty S := ⟨⟨x, hx⟩⟩
    obtain ⟨j, m, hj, hm, hov, hcol⟩ := exists_dyadic_seed_counts
      (subsetAtoms q S) b (fun i => hq i.val i.property) (fun i => hqb i.val i.property) B hB n hn
    refine ⟨j, m, hj, hm, ?_, hcol⟩
    have hmoment : (∑ i : S, (subsetAtoms q S i) ^ ((3 : ℝ) / 2)) =
        ∑ x ∈ S, (q.mass x) ^ ((3 : ℝ) / 2) :=
      Finset.sum_coe_sort S (fun x => (q.mass x) ^ ((3 : ℝ) / 2))
    rw [hmoment] at hov
    exact hov
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    letI : IsEmpty S := ⟨fun i => by simpa only [hempty, Finset.notMem_empty] using i.property⟩
    let j : S → ℕ := fun _ => 0
    let m : OccupiedCells j → ℕ := fun _ => 1
    letI : IsEmpty (OccupiedCells j) := ⟨fun l => by
      obtain ⟨i, _⟩ := cellOf_surjective j l
      exact isEmptyElim i⟩
    refine ⟨j, m, (fun i => isEmptyElim i), (fun _ => by norm_num [m]), ?_, ?_⟩
    · simpa [hempty] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb
    · have hnonneg : (0 : ℝ) ≤ 1 / (2 * B) :=
        div_nonneg (by norm_num) (mul_nonneg (by norm_num) hB.le)
      simpa using hnonneg

/-- One cell partition, seed-count vector and actual seed prior serve every
compatible ν. All displayed sample distributions are actual normalized laws. -/
theorem exists_uniform_subset_seed_compression (q ν₀ : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (f : ℝ) (hf : 0 ≤ f)
    (hscale₀ : ∀ x ∈ S, ν₀.mass x = f * q.mass x)
    (b : ℝ) (hb : 0 ≤ b) (hqb : ∀ x ∈ S, q.mass x ≤ b)
    (z : Ω) (hz : z ∉ S) (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    let ht := subset_scaled_le_one q ν₀ S f hscale₀
    ∃ (j : S → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let w := subsetCellWeights q S j f hf ht
      let p := subsetCellLaws q S hq j
      ∀ ν : Probability Ω, (∀ x ∈ S, ν.mass x = f * q.mass x) →
        (mixture w (withExterior (subsetExterior ν S z) p) = ν) ∧
        (∀ seed : SeedIndex m → Ω, 0 < (multiBinSeedPrior p m).mass seed →
          ∀ x, x ∉ S →
            (multiBinExteriorLaw w (subsetExterior ν S z) m hm seed).mass x = ν.mass x) ∧
        (∀ seed : SeedIndex m → Ω, 0 < (multiBinSeedPrior p m).mass seed →
          (∑ x ∈ S, min ((multiBinExteriorLaw w (subsetExterior ν S z) m hm seed).mass x)
            (q.mass x)) ≤
            2 * B * (n : ℝ) ^ 2 * (∑ x ∈ S, (q.mass x) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b) ∧
        FiniteTesting.totalVariation (multiBinExteriorSampleMixture w p (subsetExterior ν S z) m hm n)
          (productLaw ν n) ≤ f ^ 2 / (2 * B) := by
  dsimp only
  let ht := subset_scaled_le_one q ν₀ S f hscale₀
  obtain ⟨j, m, hj, hm, hov, hcol⟩ := exists_subset_dyadic_counts q S hq b hb hqb B hB n hn
  refine ⟨j, m, hm, ?_⟩
  dsimp only
  intro ν hscale
  let w := subsetCellWeights q S j f hf ht
  let p := subsetCellLaws q S hq j
  let exterior := subsetExterior ν S z
  have href := subsetReference_eq q ν S hq j f hf ht hscale z hz
  refine ⟨href, ?_, ?_, ?_⟩
  · intro seed hs x hx
    exact subsetCompressed_outside q ν S hq j f hf ht hscale z m hm seed hs hx
  · intro seed hs
    have hnonneg : ∀ x, 0 ≤ (if x ∈ S then q.mass x else 0) := by
      intro x
      split_ifs <;> first | exact q.nonneg x | exact le_rfl
    have hext : ∀ x, (if x ∈ S then q.mass x else 0) ≠ 0 → exterior.mass x = 0 := by
      intro x hx
      have hxS : x ∈ S := by
        by_contra hnS
        exact hx (if_neg hnS)
      exact subsetExterior_zero ν S z hz hxS
    have hraw := multiBinExteriorLaw_overlap_le_of_prior_pos w p exterior m hm seed hs
      (fun x => if x ∈ S then q.mass x else 0) hnonneg hext
      (fun l => dyadicUpper b l.val) (by
        intro l x hx
        obtain ⟨i, hi, hc⟩ := embeddedCellLaw_positive_preimage (subsetAtoms q S)
          (fun i => hq i.val i.property) j Subtype.val l x hx
        have hji : j i = l.val := congrArg Subtype.val hc
        rw [← hi]
        dsimp only
        rw [if_pos i.property]
        simpa only [subsetAtoms, hji] using hj i)
    rw [subsetOverlap_eq] at hraw
    exact hraw.trans hov
  · have h := multiBinExteriorSampleMixture_tv_le w p exterior m hm n
    rw [href] at h
    apply h.trans
    have hfactor : (∑ l, w.mass (some l) ^ 2 / (m l : ℝ)) =
        f ^ 2 * ∑ l, (cellMass (subsetAtoms q S) j l) ^ 2 / (m l : ℝ) := by
      simp only [w, subsetCellWeights, scaledCellWeights_some]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hfactor]
    calc
      _ = f ^ 2 * ((n.choose 2 : ℝ) *
          ∑ l, (cellMass (subsetAtoms q S) j l) ^ 2 / (m l : ℝ)) := by ring
      _ ≤ f ^ 2 * (1 / (2 * B)) := mul_le_mul_of_nonneg_left hcol (sq_nonneg f)
      _ = _ := by ring

/-- Caller-oriented packaging with an explicit common actual seed prior τ and
actual compressed family P(ν, seed). -/
theorem exists_uniform_subset_compression_prior (q ν₀ : Probability Ω) (S : Finset Ω)
    (hq : ∀ x ∈ S, 0 < q.mass x) (f : ℝ) (hf : 0 ≤ f)
    (hscale₀ : ∀ x ∈ S, ν₀.mass x = f * q.mass x)
    (b : ℝ) (hb : 0 ≤ b) (hqb : ∀ x ∈ S, q.mass x ≤ b)
    (z : Ω) (hz : z ∉ S) (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    let ht := subset_scaled_le_one q ν₀ S f hscale₀
    ∃ (j : S → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let cells := subsetCellLaws q S hq j
      let w := subsetCellWeights q S j f hf ht
      let τ := multiBinSeedPrior cells m
      let P := fun (ν : Probability Ω) (seed : SeedIndex m → Ω) =>
        multiBinExteriorLaw w (subsetExterior ν S z) m hm seed
      ∀ ν : Probability Ω, (∀ x ∈ S, ν.mass x = f * q.mass x) →
        (∀ seed, 0 < τ.mass seed →
          (∀ x, x ∉ S → (P ν seed).mass x = ν.mass x) ∧
          (∑ x ∈ S, min ((P ν seed).mass x) (q.mass x)) ≤
            2 * B * (n : ℝ) ^ 2 * (∑ x ∈ S, (q.mass x) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b) ∧
        FiniteTesting.totalVariation (mixture τ (fun seed => productLaw (P ν seed) n))
          (productLaw ν n) ≤ f ^ 2 / (2 * B) := by
  dsimp only
  obtain ⟨j, m, hm, h⟩ := exists_uniform_subset_seed_compression q ν₀ S hq f hf hscale₀
    b hb hqb z hz B hB n hn
  refine ⟨j, m, hm, ?_⟩
  dsimp only
  intro ν hscale
  obtain ⟨_, hout, hov, htv⟩ := h ν hscale
  exact ⟨fun seed hs => ⟨hout seed hs, hov seed hs⟩, htv⟩

end IdentityTesting.SubsetSeedCompression
