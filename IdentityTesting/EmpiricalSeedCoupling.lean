import IdentityTesting.EmpiricalSeeds
import IdentityTesting.CollisionTesting
import Mathlib.Tactic.FieldSimp

/-! Whole-sample coupling for a single cell of empirical seeds. -/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting FiniteIID CollisionTesting

universe u
variable {Ω : Type u} [Fintype Ω]

/-- Selecting distinct coordinates of an actual IID tuple gives the exact IID
law on the selected coordinates, irrespective of their order. -/
theorem productLaw_select_injective (p : Probability Ω) (m n : ℕ)
    (indices : Fin n → Fin m) (hinj : Function.Injective indices) :
    mapLaw (productLaw p m) (fun seed => seed ∘ indices) = productLaw p n := by
  classical
  have hne : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := not_nonempty_iff.mp h
    have ht := p.total
    simp at ht
  letI : Nonempty Ω := hne
  apply probability_ext
  intro y
  let b : Fin m → Ω := Function.extend indices y (fun _ => Classical.arbitrary Ω)
  have hb (j : Fin n) : b (indices j) = y j := hinj.extend_apply y _ j
  let s : Finset (Fin m) := Finset.univ.image indices
  have hevent (seed : Fin m → Ω) :
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
    (mapLaw (productLaw p m) (fun seed => seed ∘ indices)).mass y =
        mean (productLaw p m) (cylinderIndicator s b) := by
      rw [mapLaw_mass]
      unfold mean
      apply Finset.sum_congr rfl
      intro seed _
      unfold cylinderIndicator
      by_cases h : seed ∘ indices = y
      · rw [if_pos h, if_pos ((hevent seed).mp h), mul_one]
      · rw [if_neg h, if_neg (fun hc => h ((hevent seed).mpr hc)), mul_zero]
    _ = ∏ i ∈ s, p.mass (b i) := mean_productLaw_cylinder p m s b
    _ = ∏ j : Fin n, p.mass (y j) := by
      dsimp only [s]
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl
        intro j _
        rw [hb]
      · intro i _ j _ h
        exact hinj h
    _ = (productLaw p n).mass y := rfl

theorem no_repeat_univ_iff_injective {n : ℕ} (sample : Fin n → Ω) :
    ¬ HasRepeat Finset.univ sample ↔ Function.Injective sample := by
  constructor
  · intro h i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij, Finset.mem_univ _⟩
  · intro h ⟨i, j, hne, hij, _⟩
    exact hne (h hij)

/-- A whole-sample mixture bound for actual empirical seeds. The only error
event is a repeated latent seed index, not a repeated observed label. -/
theorem seedSampleMixture_tv_le (p : Probability Ω) (m : ℕ) (hm : 0 < m) (n : ℕ) :
    totalVariation (seedSampleMixture p m hm n) (productLaw p n) ≤
      (n.choose 2 : ℝ) / (m : ℝ) := by
  classical
  rw [seedSampleMixture_latent]
  calc
    totalVariation
        (mixture (productLaw (uniformFin m hm) n)
          (fun indices => mapLaw (productLaw p m) (fun seed => seed ∘ indices)))
        (productLaw p n) ≤
        ∑ indices : Fin n → Fin m,
          if Function.Injective indices then 0
          else (productLaw (uniformFin m hm) n).mass indices := by
      convert totalVariation_mixture_good_le (productLaw (uniformFin m hm) n) _ _
        Function.Injective
        (fun indices hi => productLaw_select_injective p m n indices hi) using 1
      apply Finset.sum_congr rfl
      intro indices _
      split_ifs <;> rfl
    _ = expectation (productLaw (uniformFin m hm) n) (repeatTest Finset.univ n) := by
      unfold expectation
      apply Finset.sum_congr rfl
      intro indices _
      by_cases hi : Function.Injective indices
      · have hn := (no_repeat_univ_iff_injective indices).mpr hi
        simp [hi, repeatTest, hn]
      · have hr : HasRepeat Finset.univ indices := by
          by_contra h
          exact hi ((no_repeat_univ_iff_injective indices).mp h)
        simp [hi, repeatTest, hr]
    _ ≤ (n.choose 2 : ℝ) * ∑ x : Fin m, (uniformFin m hm).mass x ^ 2 :=
      repeat_probability_le (uniformFin m hm) Finset.univ n
    _ = (n.choose 2 : ℝ) / (m : ℝ) := by
      simp only [uniformFin_mass, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
      field_simp

end IdentityTesting.EmpiricalSeeds
