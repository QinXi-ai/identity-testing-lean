import IdentityTesting.DyadicSeedLowerBound
import IdentityTesting.SubprobabilityCells
import IdentityTesting.ExteriorSeedSupport

/-! Dyadic empirical seeds on a positive subprobability with fixed exterior. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting MultiBinSeeds MultiBinExterior SeedExterior

variable {ι Ω : Type*} [Fintype ι] [Nonempty ι] [Fintype Ω]

/-- Actual normalized priors, overlap and whole-sample coupling, with the bin
partition and every integer seed count chosen internally from the atom masses. -/
theorem exists_dyadic_exterior_prior (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (b : ℝ) (hab : ∀ i, a i ≤ b) (e : ι → Ω)
    (aΩ : Ω → ℝ) (haΩ : ∀ x, 0 ≤ aΩ x) (hea : ∀ i, aΩ (e i) = a i)
    (f : ℝ) (hf : 0 ≤ f) (ht : f * ∑ i, a i ≤ 1)
    (exterior : Probability Ω) (hext : ∀ x, aΩ x ≠ 0 → exterior.mass x = 0)
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) :
    ∃ (j : ι → ℕ) (m : OccupiedCells j → ℕ) (hm : ∀ l, 0 < m l),
      let w := scaledCellWeights a (fun i => (ha i).le) j f hf ht
      let p := embeddedCellLaw a ha j e
      (∀ seed : SeedIndex m → Ω, 0 < (multiBinSeedPrior p m).mass seed →
        (∑ x, min ((multiBinExteriorLaw w exterior m hm seed).mass x) (aΩ x)) ≤
          2 * B * (n : ℝ) ^ 2 * (∑ i, (a i) ^ ((3 : ℝ) / 2)) ^ 2 + 2 * b) ∧
      FiniteTesting.totalVariation (multiBinExteriorSampleMixture w p exterior m hm n)
        (productLaw (mixture w (withExterior exterior p)) n) ≤ f ^ 2 / (2 * B) := by
  obtain ⟨j, m, hj, hm, hoverlap, hcollision⟩ :=
    exists_dyadic_seed_counts a b ha hab B hB n hn
  refine ⟨j, m, hm, ?_⟩
  dsimp only
  constructor
  · intro seed hs
    apply le_trans (multiBinExteriorLaw_overlap_le_of_prior_pos _ _ exterior m hm seed hs
      aΩ haΩ hext (fun l => dyadicUpper b l.val) ?_) hoverlap
    intro l x hx
    obtain ⟨i, hi, hicell⟩ := embeddedCellLaw_positive_preimage a ha j e l x hx
    have heq : j i = l.val := congrArg Subtype.val hicell
    rw [← hi, hea]
    simpa only [heq] using hj i
  · apply (multiBinExteriorSampleMixture_tv_le _ _ exterior m hm n).trans
    simp only [scaledCellWeights_some]
    have hfactor : (∑ l, (f * cellMass a j l) ^ 2 / (m l : ℝ)) =
        f ^ 2 * ∑ l, (cellMass a j l) ^ 2 / (m l : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hfactor]
    calc
      _ = f ^ 2 * ((n.choose 2 : ℝ) * ∑ l, (cellMass a j l) ^ 2 / (m l : ℝ)) := by ring
      _ ≤ f ^ 2 * (1 / (2 * B)) := mul_le_mul_of_nonneg_left hcollision (sq_nonneg f)
      _ = _ := by ring

end IdentityTesting.EmpiricalSeeds
