import IdentityTesting.MultiBinSeeds
import IdentityTesting.EmpiricalSeedLowerBound

/-! Support overlap of actual seed laws, including the positive-prior support condition. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting IndependentSeeds MultiBinSeeds

universe u v
variable {Ω : Type u} {I : Type v} [Fintype Ω] [Fintype I]

/-- Repeated labels can only reduce support overlap. -/
theorem mapLaw_overlap_le (w : Probability I) (seed : I → Ω)
    (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x) :
    (∑ x, min ((mapLaw w seed).mass x) (a x)) ≤ ∑ i, a (seed i) := by
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
            intro j _
            dsimp only
            split_ifs <;> first | exact ha x | exact le_rfl
      · have hz : (mapLaw w seed).mass x = 0 := by
          simp only [mapLaw_mass]
          apply Finset.sum_eq_zero
          intro i _
          exact if_neg (fun hi => hx ⟨i, hi⟩)
        rw [hz, min_eq_left (ha x)]
        exact Finset.sum_nonneg (fun i _ => by
          split_ifs <;> first | exact ha x | exact le_rfl)
    _ = ∑ i, a (seed i) := by rw [Finset.sum_comm]; simp

theorem independentLaw_positive_coordinate (p : I → Probability Ω) (seed : I → Ω)
    (hs : 0 < (independentLaw p).mass seed) (i : I) : 0 < (p i).mass (seed i) := by
  apply lt_of_le_of_ne ((p i).nonneg (seed i))
  intro hi
  have hz : (independentLaw p).mass seed = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi.symm
  exact hs.ne' hz

variable [DecidableEq I]

theorem multiBinLaw_overlap_le (w : Probability I) (m : I → ℕ) (hm : ∀ i, 0 < m i)
    (seed : SeedIndex m → Ω) (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x) (u : I → ℝ)
    (hseed : ∀ l : SeedIndex m, a (seed l) ≤ u l.1) :
    (∑ x, min ((multiBinLaw w m hm seed).mass x) (a x)) ≤ ∑ i, (m i : ℝ) * u i := by
  rw [multiBinLaw_eq_mapLaw]
  calc
    _ ≤ ∑ l : SeedIndex m, a (seed l) := mapLaw_overlap_le _ seed a ha
    _ ≤ ∑ l : SeedIndex m, u l.1 := Finset.sum_le_sum (fun l _ => hseed l)
    _ = _ := by simp [Fintype.sum_sigma]

/-- Only positive-prior seed realizations require separation. Their coordinates
automatically belong to the supports of their cell conditionals. -/
theorem multiBinLaw_overlap_le_of_prior_pos (w : Probability I) (p : I → Probability Ω)
    (m : I → ℕ) (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω)
    (hs : 0 < (multiBinSeedPrior p m).mass seed)
    (a : Ω → ℝ) (ha : ∀ x, 0 ≤ a x) (u : I → ℝ)
    (hu : ∀ i x, 0 < (p i).mass x → a x ≤ u i) :
    (∑ x, min ((multiBinLaw w m hm seed).mass x) (a x)) ≤ ∑ i, (m i : ℝ) * u i := by
  apply multiBinLaw_overlap_le w m hm seed a ha u
  intro l
  exact hu l.1 (seed l) (independentLaw_positive_coordinate _ seed hs l)

/-- A constructed multi-bin prior gives an original-model obstruction. All
statistical premises follow from cell support and scalar allocation bounds. -/
theorem no_identityTest_of_multibin_seeds {k : ℕ}
    (q : Probability (Fin k)) (w : Probability I) (p : I → Probability (Fin k))
    (hq : mixture w p = q) (m : I → ℕ) (hm : ∀ i, 0 < m i)
    (u : I → ℝ) (hu : ∀ i x, 0 < (p i).mass x → q.mass x ≤ u i)
    (ε : ℝ) (n : ℕ) (hgap : (∑ i, (m i : ℝ) * u i) < 1 - ε)
    (hsample : (n.choose 2 : ℝ) * (∑ i, w.mass i ^ 2 / (m i : ℝ)) < (1 : ℝ) / 3) :
    ¬ IdentityTesting.HasIdentityTest (IdentityTesting.extendFiniteLaw q) ε n := by
  apply IdentityTesting.no_identityTest_extendFiniteLaw_of_finite_prior
    (multiBinSeedPrior p m) (multiBinLaw w m hm) q ε n
  · intro seed hs
    rw [finite_totalVariation_eq_one_sub_overlap]
    have h := multiBinLaw_overlap_le_of_prior_pos w p m hm seed hs q.mass q.nonneg u hu
    linarith
  · have h := (multiBinSampleMixture_tv_le w p m hm n).trans_lt hsample
    rw [hq] at h
    exact h

end IdentityTesting.EmpiricalSeeds
