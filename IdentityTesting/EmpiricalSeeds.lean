import IdentityTesting.FiniteCoupling

/-!
# Actual empirical seed priors

The reference seed vector has its actual IID law. The empirical law is its
pushforward of a uniform seed index, not a probability law supplied together
with unproved normalization. The latent-index representation below concerns the
entire fixed-size sample mixture and supplies the representation used by the
injective-index marginal and repeat-probability estimates.
-/

noncomputable section
namespace IdentityTesting.EmpiricalSeeds
open scoped BigOperators
open Classical
open FiniteTesting

universe u
variable {Ω : Type u} [Fintype Ω]

def uniformFin (m : ℕ) (hm : 0 < m) : Probability (Fin m) where
  mass _ := 1 / (m : ℝ)
  nonneg _ := div_nonneg (by norm_num) (Nat.cast_nonneg m)
  total := by
    simp [Nat.ne_of_gt hm]

@[simp] theorem uniformFin_mass (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (uniformFin m hm).mass j = 1 / (m : ℝ) := rfl

def empiricalLaw {m : ℕ} (hm : 0 < m) (seed : Fin m → Ω) : Probability Ω :=
  mapLaw (uniformFin m hm) seed

theorem empiricalLaw_mass {m : ℕ} (hm : 0 < m) (seed : Fin m → Ω) (x : Ω) :
    (empiricalLaw hm seed).mass x = ∑ j, if seed j = x then 1 / (m : ℝ) else 0 := by
  simp only [empiricalLaw, mapLaw_mass, uniformFin_mass]

theorem empiricalLaw_mass_zero {m : ℕ} (hm : 0 < m) (seed : Fin m → Ω) (x : Ω)
    (hx : x ∉ Finset.univ.image seed) : (empiricalLaw hm seed).mass x = 0 := by
  rw [empiricalLaw_mass]
  apply Finset.sum_eq_zero
  intro j _
  have hj : seed j ≠ x := by
    intro h
    apply hx
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩
  simp [hj]

/-- Every realization has overlap at most the number of seeds times the largest
reference mass in the cell. Repeated seeds only reduce the possible support. -/
theorem empiricalLaw_overlap_le {m : ℕ} (hm : 0 < m) (seed : Fin m → Ω)
    (a : Ω → ℝ) (b : ℝ) (ha : ∀ x, 0 ≤ a x) (hab : ∀ x, a x ≤ b) (hb : 0 ≤ b) :
    (∑ x, min ((empiricalLaw hm seed).mass x) (a x)) ≤ (m : ℝ) * b := by
  classical
  let s := Finset.univ.image seed
  calc
    (∑ x, min ((empiricalLaw hm seed).mass x) (a x)) ≤
        ∑ x, if x ∈ s then a x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ s
      · simpa only [hx, ite_true] using min_le_right ((empiricalLaw hm seed).mass x) (a x)
      · rw [empiricalLaw_mass_zero hm seed x hx, min_eq_left (ha x), if_neg hx]
    _ = ∑ x ∈ s, a x := by simp
    _ ≤ (s.card : ℝ) * b := by
      calc
        (∑ x ∈ s, a x) ≤ ∑ _x ∈ s, b := Finset.sum_le_sum fun x _ => hab x
        _ = _ := by simp
    _ ≤ (m : ℝ) * b := by
      apply mul_le_mul_of_nonneg_right _ hb
      exact_mod_cast (Finset.card_image_le (s := Finset.univ) (f := seed)).trans_eq
        (Fintype.card_fin m)

/-- The actual prior predictive law of n observations from m empirical seeds. -/
def seedSampleMixture (p : Probability Ω) (m : ℕ) (hm : 0 < m) (n : ℕ) :
    Probability (Fin n → Ω) :=
  mixture (productLaw p m) (fun seed => productLaw (empiricalLaw hm seed) n)

/-- Reorder actual finite sums to expose all latent seed indices at once. -/
theorem seedSampleMixture_latent (p : Probability Ω) (m : ℕ) (hm : 0 < m) (n : ℕ) :
    seedSampleMixture p m hm n =
      mixture (productLaw (uniformFin m hm) n)
        (fun indices => mapLaw (productLaw p m) (fun seed => seed ∘ indices)) := by
  have hcond : ∀ seed : Fin m → Ω, productLaw (empiricalLaw hm seed) n =
      mapLaw (productLaw (uniformFin m hm) n) (fun indices => seed ∘ indices) := by
    intro seed
    exact (mapLaw_productLaw (uniformFin m hm) seed n).symm
  apply probability_ext
  intro sample
  simp only [seedSampleMixture, mixture_mass, hcond, mapLaw, mixture_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro indices _
  apply Finset.sum_congr rfl
  intro seed _
  ring

end IdentityTesting.EmpiricalSeeds
