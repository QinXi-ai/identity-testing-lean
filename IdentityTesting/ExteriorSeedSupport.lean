import IdentityTesting.MultiBinExterior
import IdentityTesting.SeedSupport

/-! Support overlap for a seed-compressed part with a fixed disjoint exterior. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting IndependentSeeds MultiBinSeeds SeedExterior MultiBinExterior

universe u v
variable {Ω : Type u} {I : Type v} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem exteriorSeedLaw_overlap_le (w : Probability (Option I)) (exterior : Probability Ω)
    (seed : I → Ω) (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hext : ∀ x, a x ≠ 0 → exterior.mass x = 0) :
    (∑ x, min ((exteriorSeedLaw w exterior seed).mass x) (a x)) ≤
      ∑ i, a (seed i) := by
  calc
    _ ≤ ∑ x, ∑ i, if seed i = x then a x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : ∃ i, seed i = x
      · obtain ⟨i, hi⟩ := hx
        apply (min_le_right _ _).trans
        calc
          a x = (if seed i = x then a x else 0) := (if_pos hi).symm
          _ ≤ ∑ i, if seed i = x then a x else 0 := by
            apply Finset.single_le_sum (f := fun i => if seed i = x then a x else 0)
              (s := Finset.univ) ?_ (Finset.mem_univ i)
            intro l _
            dsimp only
            split_ifs <;> first | exact ha x | exact le_rfl
      · have hzero : min ((exteriorSeedLaw w exterior seed).mass x) (a x) = 0 := by
          by_cases ha0 : a x = 0
          · rw [ha0, min_eq_right ((exteriorSeedLaw w exterior seed).nonneg x)]
          · have he : exterior.mass x = 0 := hext x ha0
            have hn : ∀ i, x ≠ seed i := fun i hi => hx ⟨i, hi.symm⟩
            have hz : (exteriorSeedLaw w exterior seed).mass x = 0 := by
              simp [exteriorSeedLaw, mixture_mass, Fintype.sum_option,
                conditionalLaw, pointLaw_mass, he, hn]
            rw [hz, min_eq_left (ha x)]
        rw [hzero]
        exact Finset.sum_nonneg (fun i _ => by
          split_ifs <;> first | exact ha x | exact le_rfl)
    _ = _ := by rw [Finset.sum_comm]; simp

theorem multiBinExteriorLaw_overlap_le_of_prior_pos (w : Probability (Option I))
    (p : I → Probability Ω) (exterior : Probability Ω) (m : I → ℕ)
    (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω)
    (hs : 0 < (multiBinSeedPrior p m).mass seed)
    (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hext : ∀ x, a x ≠ 0 → exterior.mass x = 0)
    (u : I → ℝ) (hu : ∀ i x, 0 < (p i).mass x → a x ≤ u i) :
    (∑ x, min ((multiBinExteriorLaw w exterior m hm seed).mass x) (a x)) ≤
      ∑ i, (m i : ℝ) * u i := by
  rw [multiBinExteriorLaw_eq]
  calc
    _ ≤ ∑ l : SeedIndex m, a (seed l) := exteriorSeedLaw_overlap_le _ exterior seed a ha hext
    _ ≤ ∑ l : SeedIndex m, u l.1 := by
      apply Finset.sum_le_sum
      intro l _
      exact hu l.1 (seed l) (independentLaw_positive_coordinate _ seed hs l)
    _ = _ := by simp [Fintype.sum_sigma]

end IdentityTesting.EmpiricalSeeds
