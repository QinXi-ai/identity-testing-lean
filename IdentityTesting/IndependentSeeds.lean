import IdentityTesting.EmpiricalSeeds
import IdentityTesting.CollisionTesting

/-!
# Independently distributed finite seeds
An arbitrary finite latent index has its own observation law. Reusing an index
reuses its seed, whereas distinct indices expose independent observations.
-/

noncomputable section
namespace IdentityTesting.IndependentSeeds
open scoped BigOperators
open Classical
open FiniteTesting FiniteIID CollisionTesting

universe u v
variable {Ω : Type u} {I : Type v} [Fintype Ω] [Fintype I] [DecidableEq I]

/-- The actual product of a finite family of possibly different laws. -/
def independentLaw (p : I → Probability Ω) : Probability (I → Ω) where
  mass seed := ∏ i, (p i).mass (seed i)
  nonneg seed := Finset.prod_nonneg fun i _ => (p i).nonneg (seed i)
  total := by
    rw [← Fintype.prod_sum]
    simp only [Probability.total, Finset.prod_const_one]

@[simp] theorem independentLaw_mass (p : I → Probability Ω) (seed : I → Ω) :
    (independentLaw p).mass seed = ∏ i, (p i).mass (seed i) := rfl

private theorem probability_nonempty (p : Probability Ω) : Nonempty Ω := by
  by_contra h
  haveI : IsEmpty Ω := not_nonempty_iff.mp h
  have ht := p.total
  simp at ht

/-- A coordinate cylinder under nonidentically distributed independent seeds. -/
theorem independentLaw_cylinder (p : I → Probability Ω) (s : Finset I) (b : I → Ω) :
    (∑ seed, (independentLaw p).mass seed *
      (if ∀ i ∈ s, seed i = b i then (1 : ℝ) else 0)) =
      ∏ i ∈ s, (p i).mass (b i) := by
  classical
  have hind (seed : I → Ω) :
      (if ∀ i ∈ s, seed i = b i then (1 : ℝ) else 0) =
        ∏ i, if i ∈ s then (if seed i = b i then (1 : ℝ) else 0) else 1 := by
    rw [Finset.prod_ite]
    simp only [Finset.filter_univ_mem, Finset.prod_const_one, mul_one, Finset.prod_boole]
    split_ifs <;> rfl
  simp only [hind, independentLaw_mass, ← Finset.prod_mul_distrib]
  calc
    (∑ seed : I → Ω, ∏ i, (p i).mass (seed i) *
        (if i ∈ s then (if seed i = b i then (1 : ℝ) else 0) else 1)) =
      ∏ i, ∑ x, (p i).mass x *
        (if i ∈ s then (if x = b i then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum (fun i x => (p i).mass x *
        (if i ∈ s then (if x = b i then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then (p i).mass (b i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [hi, mul_ite]
      · simp [hi, (p i).total]
    _ = _ := by simp

/-- Distinct queried indices have exactly their corresponding independent laws. -/
theorem independentLaw_select_injective (p : I → Probability Ω) (n : ℕ)
    (indices : Fin n → I) (hinj : Function.Injective indices) :
    mapLaw (independentLaw p) (fun seed => seed ∘ indices) =
      independentLaw (fun j => p (indices j)) := by
  classical
  apply probability_ext
  intro y
  let b : I → Ω := Function.extend indices y
    (fun i => Classical.choice (probability_nonempty (p i)))
  have hb (j : Fin n) : b (indices j) = y j := hinj.extend_apply y _ j
  let s : Finset I := Finset.univ.image indices
  have hevent (seed : I → Ω) :
      seed ∘ indices = y ↔ ∀ i ∈ s, seed i = b i := by
    constructor
    · intro h i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      rw [hb]
      exact congr_fun h j
    · intro h
      apply funext
      intro j
      exact (h (indices j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).trans (hb j)
  calc
    (mapLaw (independentLaw p) (fun seed => seed ∘ indices)).mass y =
        ∑ seed, (independentLaw p).mass seed *
          (if ∀ i ∈ s, seed i = b i then (1 : ℝ) else 0) := by
      rw [mapLaw_mass]
      apply Finset.sum_congr rfl
      intro seed _
      by_cases h : seed ∘ indices = y
      · rw [if_pos h, if_pos ((hevent seed).mp h), mul_one]
      · rw [if_neg h, if_neg (fun hc => h ((hevent seed).mpr hc)), mul_zero]
    _ = ∏ i ∈ s, (p i).mass (b i) := independentLaw_cylinder p s b
    _ = ∏ j : Fin n, (p (indices j)).mass (y j) := by
      dsimp only [s]
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro j _
        rw [hb]
      · intro i _ j _ h
        exact hinj h
    _ = (independentLaw (fun j => p (indices j))).mass y := rfl

omit [DecidableEq I] in
/-- Averaging independent conditional coordinates yields the actual IID mixture. -/
theorem mixture_independentLaw (r : Probability I) (p : I → Probability Ω) (n : ℕ) :
    mixture (productLaw r n) (fun indices => independentLaw (fun j => p (indices j))) =
      productLaw (mixture r p) n := by
  apply probability_ext
  intro y
  simp only [mixture_mass, productLaw_mass, independentLaw_mass]
  calc
    (∑ indices : Fin n → I,
        (∏ j, r.mass (indices j)) * ∏ j, (p (indices j)).mass (y j)) =
        ∑ indices : Fin n → I, ∏ j, r.mass (indices j) * (p (indices j)).mass (y j) := by
      apply Finset.sum_congr rfl
      intro indices _
      rw [Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum (fun j i => r.mass i * (p i).mass (y j))).symm

/-- Actual prior predictive law obtained by reusing the independently drawn seeds. -/
def independentSeedMixture (r : Probability I) (p : I → Probability Ω) (n : ℕ) :
    Probability (Fin n → Ω) :=
  mixture (independentLaw p) (fun seed => productLaw (mapLaw r seed) n)

theorem independentSeedMixture_latent (r : Probability I) (p : I → Probability Ω) (n : ℕ) :
    independentSeedMixture r p n =
      mixture (productLaw r n)
        (fun indices => mapLaw (independentLaw p) (fun seed => seed ∘ indices)) := by
  have hcond : ∀ seed : I → Ω, productLaw (mapLaw r seed) n =
      mapLaw (productLaw r n) (fun indices => seed ∘ indices) := by
    intro seed
    exact (mapLaw_productLaw r seed n).symm
  apply probability_ext
  intro sample
  simp only [independentSeedMixture, mixture_mass]
  simp_rw [hcond]
  simp only [mapLaw, mixture_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro indices _
  apply Finset.sum_congr rfl
  intro seed _
  ring

omit [DecidableEq I] in
private theorem no_repeat_iff_injective {n : ℕ} (indices : Fin n → I) :
    ¬ HasRepeat Finset.univ indices ↔ Function.Injective indices := by
  constructor
  · intro h i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij, Finset.mem_univ _⟩
  · intro h ⟨i, j, hne, hij, _⟩
    exact hne (h hij)

/-- A whole fixed-size sample bound with no shared-support restriction. -/
theorem independentSeedMixture_tv_le (r : Probability I) (p : I → Probability Ω) (n : ℕ) :
    totalVariation (independentSeedMixture r p n) (productLaw (mixture r p) n) ≤
      (n.choose 2 : ℝ) * ∑ i, r.mass i ^ 2 := by
  classical
  rw [independentSeedMixture_latent, ← mixture_independentLaw]
  calc
    totalVariation
        (mixture (productLaw r n)
          (fun indices => mapLaw (independentLaw p) (fun seed => seed ∘ indices)))
        (mixture (productLaw r n)
          (fun indices => independentLaw (fun j => p (indices j)))) ≤
        ∑ indices : Fin n → I,
          if Function.Injective indices then 0 else (productLaw r n).mass indices := by
      convert totalVariation_mixtures_agree_le (productLaw r n) _ _ Function.Injective
        (fun indices hi => independentLaw_select_injective p n indices hi) using 1
      apply Finset.sum_congr rfl
      intro indices _
      split_ifs <;> rfl
    _ = expectation (productLaw r n) (repeatTest Finset.univ n) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro indices _
      by_cases hi : Function.Injective indices
      · have hn := (no_repeat_iff_injective indices).mpr hi
        simp [hi, repeatTest, hn]
      · have hr : HasRepeat Finset.univ indices := by
          by_contra h
          exact hi ((no_repeat_iff_injective indices).mp h)
        simp [hi, repeatTest, hr]
    _ ≤ _ := repeat_probability_le r Finset.univ n

end IdentityTesting.IndependentSeeds
