import IdentityTesting.IndependentSeeds
import Mathlib.Tactic.FieldSimp

/-!
# Actual multi-bin empirical seed priors
All seeds, including seeds from different cells, are independent. Cells may
have overlapping observation supports. The bound compares entire fixed-size
sample laws and follows from repeated latent seed indices.
-/

noncomputable section
namespace IdentityTesting.MultiBinSeeds
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds IndependentSeeds

universe u v
variable {Ω : Type u} {B : Type v} [Fintype Ω] [Fintype B] [DecidableEq B]

abbrev SeedIndex (m : B → ℕ) := (i : B) × Fin (m i)

/-- A cell has mass w_i, split uniformly among its m_i latent seed indices. -/
def latentWeights (w : Probability B) (m : B → ℕ) (hm : ∀ i, 0 < m i) :
    Probability (SeedIndex m) where
  mass l := w.mass l.1 / (m l.1 : ℝ)
  nonneg l := div_nonneg (w.nonneg l.1) (Nat.cast_nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    calc
      (∑ i, ∑ _j : Fin (m i), w.mass i / (m i : ℝ)) = ∑ i, w.mass i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
        field_simp
      _ = 1 := w.total

omit [DecidableEq B] in
@[simp] theorem latentWeights_mass (w : Probability B) (m : B → ℕ)
    (hm : ∀ i, 0 < m i) (l : SeedIndex m) :
    (latentWeights w m hm).mass l = w.mass l.1 / (m l.1 : ℝ) := rfl

/-- The actual independently drawn seed prior. -/
def multiBinSeedPrior (p : B → Probability Ω) (m : B → ℕ) :
    Probability (SeedIndex m → Ω) :=
  independentLaw (fun l : SeedIndex m => p l.1)

/-- Each prior member mixes the actual empirical distribution in each cell. -/
def multiBinLaw (w : Probability B) (m : B → ℕ) (hm : ∀ i, 0 < m i)
    (seed : SeedIndex m → Ω) : Probability Ω :=
  mixture w (fun i => empiricalLaw (hm i) (fun j => seed ⟨i, j⟩))

omit [DecidableEq B] in
theorem multiBinLaw_eq_mapLaw (w : Probability B) (m : B → ℕ) (hm : ∀ i, 0 < m i)
    (seed : SeedIndex m → Ω) :
    multiBinLaw w m hm seed = mapLaw (latentWeights w m hm) seed := by
  classical
  apply probability_ext
  intro x
  simp only [multiBinLaw, mixture_mass, empiricalLaw_mass, mapLaw_mass,
    Fintype.sum_sigma, latentWeights_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

omit [DecidableEq B] in
theorem latentWeights_mixture (w : Probability B) (p : B → Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) :
    mixture (latentWeights w m hm) (fun l : SeedIndex m => p l.1) = mixture w p := by
  apply probability_ext
  intro x
  simp only [mixture_mass, latentWeights_mass, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
  field_simp

omit [DecidableEq B] in
theorem latentWeights_square_sum (w : Probability B) (m : B → ℕ) (hm : ∀ i, 0 < m i) :
    (∑ l : SeedIndex m, (latentWeights w m hm).mass l ^ 2) =
      ∑ i, w.mass i ^ 2 / (m i : ℝ) := by
  simp only [latentWeights_mass, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmi : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hm i))
  field_simp

/-- Actual full n-sample prior predictive law. -/
def multiBinSampleMixture (w : Probability B) (p : B → Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    Probability (Fin n → Ω) :=
  mixture (multiBinSeedPrior p m) (fun seed => productLaw (multiBinLaw w m hm seed) n)

theorem multiBinSampleMixture_eq_independent (w : Probability B) (p : B → Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    multiBinSampleMixture w p m hm n =
      independentSeedMixture (latentWeights w m hm) (fun l : SeedIndex m => p l.1) n := by
  unfold multiBinSampleMixture multiBinSeedPrior independentSeedMixture
  congr 1
  funext seed
  rw [multiBinLaw_eq_mapLaw]

/-- Whole fixed-sample TV bound for actual independent multi-bin empirical
priors; repeated observed labels and overlapping cell supports are allowed. -/
theorem multiBinSampleMixture_tv_le (w : Probability B) (p : B → Probability Ω)
    (m : B → ℕ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    totalVariation (multiBinSampleMixture w p m hm n) (productLaw (mixture w p) n) ≤
      (n.choose 2 : ℝ) * ∑ i, w.mass i ^ 2 / (m i : ℝ) := by
  rw [multiBinSampleMixture_eq_independent]
  calc
    totalVariation
        (independentSeedMixture (latentWeights w m hm) (fun l : SeedIndex m => p l.1) n)
        (productLaw (mixture w p) n) =
      totalVariation
        (independentSeedMixture (latentWeights w m hm) (fun l : SeedIndex m => p l.1) n)
        (productLaw
          (mixture (latentWeights w m hm) (fun l : SeedIndex m => p l.1)) n) := by
      rw [latentWeights_mixture]
    _ ≤ (n.choose 2 : ℝ) * ∑ l : SeedIndex m, (latentWeights w m hm).mass l ^ 2 :=
      independentSeedMixture_tv_le (latentWeights w m hm) (fun l : SeedIndex m => p l.1) n
    _ = _ := by rw [latentWeights_square_sum]

end IdentityTesting.MultiBinSeeds
