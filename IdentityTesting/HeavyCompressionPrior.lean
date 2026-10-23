import IdentityTesting.HeavyCompressionFeasible
import IdentityTesting.SubsetSeedCompression

/-! `hh:compression` with the existing actual dyadic seed prior.
This is a caller wrapper: it specializes the established construction to S,
the actual maximum a_max, and the original feasible-allocation constants. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting.HeavyCompressionFeasible
open Classical
open FiniteTesting HeavySignedFamily HeavyLowerGeometry SubsetSeedCompression
open EmpiricalSeeds MultiBinSeeds MultiBinExterior SeedExterior

variable {k : ℕ}

/-- Original compression lemma for positive integer sample sizes. The entire
dyadic prior is supplied by the existing construction, also for empty S. -/
theorem exists_feasible_compression_prior
    (q ν : Probability (Fin (k + 1))) (x : Fin k → ℝ)
    (hq : ∀ i, 0 < q.mass i) (hx : ∀ i, 0 ≤ x i ∧ x i < 1) {T : ℝ} (hT : 0 < T)
    (hbudget : T ^ 2 * (∑ i, q.mass i.succ ^ 2 * x i ^ 4 / (1 - x i ^ 4)) ≤ 1)
    (f : ℝ) (hf1 : 1 ≤ f) (hf2 : f ≤ 2)
    (hscale : ∀ i ∈ seedSet x, ν.mass i = f * q.mass i)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ((∑ i, q.mass i.succ * x i) = lowDisplacement q x + highMass q x - highSlack q x) ∧
    (T ^ 2 * (∑ i ∈ highTail x, q.mass i.succ ^ ((3 : ℝ) / 2)) ^ 2 ≤ 1024 * highSlack q x) ∧
    (highAtomMax q x < 16 / T) ∧
    let hqS := fun i (_ : i ∈ seedSet x) => hq i
    let hf : 0 ≤ f := le_trans (by norm_num) hf1
    let ht := subset_scaled_le_one q ν (seedSet x) f hscale
    ∃ (j : seedSet x → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let cells := subsetCellLaws q (seedSet x) hqS j
      let w := subsetCellWeights q (seedSet x) j f hf ht
      let τ := multiBinSeedPrior cells m
      let P := fun seed : SeedIndex m → Fin (k + 1) =>
        multiBinExteriorLaw w (subsetExterior ν (seedSet x) 0) m hm seed
      (∀ seed, 0 < τ.mass seed →
        (∀ i, i ∉ seedSet x → (P seed).mass i = ν.mass i) ∧
        (∑ i ∈ seedSet x, min ((P seed).mass i) (q.mass i)) ≤
          2 * B * (n : ℝ) ^ 2 * (∑ i ∈ highTail x, q.mass i.succ ^ ((3 : ℝ) / 2)) ^ 2 +
            2 * highAtomMax q x) ∧
      FiniteTesting.totalVariation (mixture τ (fun seed => productLaw (P seed) n))
        (productLaw ν n) ≤ f ^ 2 / (2 * B) := by
  have hg := compression_geometry q x hq hx hT hbudget
  refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
  dsimp only
  have hf : 0 ≤ f := by linarith
  obtain ⟨j, m, hm, h⟩ := exists_uniform_subset_compression_prior q ν (seedSet x)
    (fun i _ => hq i) f hf hscale (highAtomMax q x) (highAtomMax_nonneg q x)
    (seed_atom_le_max q x) 0 (head_not_seedSet x) B hB n hn
  refine ⟨j, m, hm, ?_⟩
  simpa only [sum_seedSet] using h ν hscale

end IdentityTesting.HeavyCompressionFeasible
