import IdentityTesting.SeedExterior

/-! Actual multi-bin seed priors with an unchanged fixed exterior law. -/

noncomputable section
namespace IdentityTesting.MultiBinExterior
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds IndependentSeeds MultiBinSeeds SeedExterior

universe u v
variable {Ω : Type u} {B : Type v} [Fintype Ω] [Fintype B] [DecidableEq B]

/-- None selects the fixed exterior. Every bin's mass is split uniformly among
its latent seed indices. -/
def exteriorLatentWeights (w : Probability (Option B)) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) : Probability (Option (SeedIndex m)) where
  mass
    | none => w.mass none
    | some l => w.mass (some l.1) / (m l.1 : ℝ)
  nonneg l := by
    cases l with
    | none => exact w.nonneg none
    | some l => exact div_nonneg (w.nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [Fintype.sum_option, Fintype.sum_sigma]
    have hs : (∑ i, ∑ _j : Fin (m i), w.mass (some i) / (m i : ℝ)) =
        ∑ i, w.mass (some i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
      field_simp
    rw [hs]
    simpa only [Fintype.sum_option] using w.total

omit [DecidableEq B] in
@[simp] theorem exteriorLatentWeights_none (w : Probability (Option B)) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) : (exteriorLatentWeights w m hm).mass none = w.mass none := rfl

omit [DecidableEq B] in
@[simp] theorem exteriorLatentWeights_some (w : Probability (Option B)) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) (l : SeedIndex m) :
    (exteriorLatentWeights w m hm).mass (some l) =
      w.mass (some l.1) / (m l.1 : ℝ) := rfl

/-- The fixed exterior is unchanged in every actual prior member. -/
def multiBinExteriorLaw (w : Probability (Option B)) (exterior : Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω) : Probability Ω :=
  mixture w (withExterior exterior
    (fun i => empiricalLaw (hm i) (fun j => seed ⟨i, j⟩)))

omit [DecidableEq B] in
theorem multiBinExteriorLaw_eq (w : Probability (Option B)) (exterior : Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (seed : SeedIndex m → Ω) :
    multiBinExteriorLaw w exterior m hm seed =
      exteriorSeedLaw (exteriorLatentWeights w m hm) exterior seed := by
  classical
  apply probability_ext
  intro x
  simp only [multiBinExteriorLaw, exteriorSeedLaw, mixture_mass, Fintype.sum_option,
    exteriorLatentWeights_none, exteriorLatentWeights_some]
  change w.mass none * exterior.mass x +
      (∑ i, w.mass (some i) * (empiricalLaw (hm i) (fun j => seed ⟨i, j⟩)).mass x) =
    w.mass none * exterior.mass x +
      ∑ l : SeedIndex m, (w.mass (some l.1) / (m l.1 : ℝ)) * (pointLaw (seed l)).mass x
  congr 1
  simp only [empiricalLaw_mass, Fintype.sum_sigma, Finset.mul_sum, pointLaw_mass]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : seed ⟨i, j⟩ = x
  · simp [h, div_eq_mul_inv]
  · simp [h, Ne.symm h, div_eq_mul_inv]

omit [DecidableEq B] in
theorem exteriorLatentWeights_mixture (w : Probability (Option B))
    (p : B → Probability Ω) (exterior : Probability Ω) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) :
    mixture (exteriorLatentWeights w m hm)
      (withExterior exterior (fun l : SeedIndex m => p l.1)) =
      mixture w (withExterior exterior p) := by
  apply probability_ext
  intro x
  simp only [mixture_mass, Fintype.sum_option,
    exteriorLatentWeights_none, exteriorLatentWeights_some]
  change w.mass none * exterior.mass x +
      (∑ l : SeedIndex m, w.mass (some l.1) / (m l.1 : ℝ) * (p l.1).mass x) =
    w.mass none * exterior.mass x + ∑ i, w.mass (some i) * (p i).mass x
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
  field_simp

omit [DecidableEq B] in
theorem exteriorLatentWeights_square_sum (w : Probability (Option B))
    (m : B → ℕ) (hm : ∀ i, 0 < m i) :
    (∑ l : SeedIndex m, (exteriorLatentWeights w m hm).mass (some l) ^ 2) =
      ∑ i, w.mass (some i) ^ 2 / (m i : ℝ) := by
  simp only [exteriorLatentWeights_some, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
  field_simp

def multiBinExteriorSampleMixture (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    Probability (Fin n → Ω) :=
  mixture (multiBinSeedPrior p m)
    (fun seed => productLaw (multiBinExteriorLaw w exterior m hm seed) n)

theorem multiBinExteriorSampleMixture_eq (w : Probability (Option B)) (p : B → Probability Ω)
    (exterior : Probability Ω) (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    multiBinExteriorSampleMixture w p exterior m hm n =
      exteriorSeedMixture (exteriorLatentWeights w m hm)
        (fun l : SeedIndex m => p l.1) exterior n := by
  unfold multiBinExteriorSampleMixture exteriorSeedMixture multiBinSeedPrior
  congr 1
  funext seed
  rw [multiBinExteriorLaw_eq]

/-- Entire fixed-sample law comparison with actual independent seeds and a fixed
exterior. Exterior repeats incur no additional error. -/
theorem multiBinExteriorSampleMixture_tv_le (w : Probability (Option B))
    (p : B → Probability Ω) (exterior : Probability Ω) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) (n : ℕ) :
    totalVariation (multiBinExteriorSampleMixture w p exterior m hm n)
      (productLaw (mixture w (withExterior exterior p)) n) ≤
      (n.choose 2 : ℝ) * ∑ i, w.mass (some i) ^ 2 / (m i : ℝ) := by
  rw [multiBinExteriorSampleMixture_eq]
  calc
    totalVariation
        (exteriorSeedMixture (exteriorLatentWeights w m hm)
          (fun l : SeedIndex m => p l.1) exterior n)
        (productLaw (mixture w (withExterior exterior p)) n) =
      totalVariation
        (exteriorSeedMixture (exteriorLatentWeights w m hm)
          (fun l : SeedIndex m => p l.1) exterior n)
        (productLaw
          (mixture (exteriorLatentWeights w m hm)
            (withExterior exterior (fun l : SeedIndex m => p l.1))) n) := by
      rw [exteriorLatentWeights_mixture]
    _ ≤ (n.choose 2 : ℝ) *
        ∑ l : SeedIndex m, (exteriorLatentWeights w m hm).mass (some l) ^ 2 :=
      exteriorSeedMixture_tv_le _ _ exterior n
    _ = _ := by rw [exteriorLatentWeights_square_sum]

end IdentityTesting.MultiBinExterior
