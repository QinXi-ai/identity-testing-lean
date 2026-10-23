import IdentityTesting.FiniteSampleMaps

/-! Finite common-randomness couplings for actual observation laws. -/

noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
open Classical

universe u v w
variable {Ω : Type u} {Ξ : Type v} {I : Type w}
variable [Fintype Ω] [Fintype Ξ] [Fintype I]

@[simp] theorem totalVariation_self (p : Probability Ω) : totalVariation p p = 0 := by
  simp [totalVariation]

theorem totalVariation_le_one (p q : Probability Ω) : totalVariation p q ≤ 1 := by
  calc
    totalVariation p q ≤ (1 / 2 : ℝ) * ∑ x, (p.mass x + q.mass x) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro x _
      calc
        |p.mass x - q.mass x| ≤ |p.mass x| + |q.mass x| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg (p.nonneg x), abs_of_nonneg (q.nonneg x)]
    _ = 1 := by rw [Finset.sum_add_distrib, p.total, q.total]; norm_num

/-- Two observations constructed using the same finite random source differ in
law by at most their actual mismatch probability. -/
theorem totalVariation_common_randomness_le (p : Probability Ω) (f g : Ω → Ξ) :
    totalVariation (mapLaw p f) (mapLaw p g) ≤
      ∑ x, if f x ≠ g x then p.mass x else 0 := by
  have h := totalVariation_mixtures_same_weights p
    (fun x => pointLaw (f x)) (fun x => pointLaw (g x))
  change totalVariation (mapLaw p f) (mapLaw p g) ≤ _ at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro x _
  rw [totalVariation_pointLaw]
  by_cases hx : f x = g x <;> simp [hx]

/-- If actual conditional laws agree on a good event, their whole mixtures are
within the probability of its complement. -/
theorem totalVariation_mixtures_agree_le (weights : Probability I)
    (p q : I → Probability Ω) (good : I → Prop)
    (hgood : ∀ i, good i → p i = q i) :
    totalVariation (mixture weights p) (mixture weights q) ≤
      ∑ i, if good i then 0 else weights.mass i := by
  refine (totalVariation_mixtures_same_weights weights p q).trans ?_
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : good i
  · simp [hi, hgood i hi]
  · simp only [hi, ite_false]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (totalVariation_le_one (p i) (q i)) (weights.nonneg i)

@[simp] theorem mixture_constant (weights : Probability I) (p : Probability Ω) :
    mixture weights (fun _ => p) = p := by
  apply probability_ext
  intro x
  simp only [mixture_mass, ← Finset.sum_mul, weights.total, one_mul]

/-- A mixture matches a fixed law on a good latent event. In seed constructions,
the good event will be that the queried seed indices are all distinct. -/
theorem totalVariation_mixture_good_le (weights : Probability I)
    (laws : I → Probability Ω) (q : Probability Ω) (good : I → Prop)
    (hgood : ∀ i, good i → laws i = q) :
    totalVariation (mixture weights laws) q ≤
      ∑ i, if good i then 0 else weights.mass i := by
  simpa only [mixture_constant] using
    totalVariation_mixtures_agree_le weights laws (fun _ => q) good hgood

end IdentityTesting.FiniteTesting
