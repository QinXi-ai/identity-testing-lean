import IdentityTesting.FiniteTesting
import Mathlib.Algebra.BigOperators.Fin

/-! Tensorization of total variation for finite categorical product laws. -/
noncomputable section
namespace IdentityTesting.FiniteTesting
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

theorem productLaw_l1_succ_le (p q : Probability Ω) (n : ℕ) :
    (∑ x, |(productLaw p (n + 1)).mass x - (productLaw q (n + 1)).mass x|) ≤
      (∑ x, |(productLaw p n).mass x - (productLaw q n).mass x|) +
      ∑ i, |p.mass i - q.mass i| := by
  let e : Ω × (Fin n → Ω) ≃ (Fin (n + 1) → Ω) := Fin.consEquiv (fun _ => Ω)
  rw [← e.sum_comp (fun x => |(productLaw p (n + 1)).mass x - (productLaw q (n + 1)).mass x|)]
  have hb : ∀ z : Ω × (Fin n → Ω),
      |(productLaw p (n + 1)).mass (e z) - (productLaw q (n + 1)).mass (e z)| ≤
      p.mass z.1 * |(productLaw p n).mass z.2 - (productLaw q n).mass z.2| +
        |p.mass z.1 - q.mass z.1| * (productLaw q n).mass z.2 := by
    intro z
    simp only [productLaw_mass, e, Fin.consEquiv_apply, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    change |p.mass z.1 * (productLaw p n).mass z.2 - q.mass z.1 * (productLaw q n).mass z.2| ≤ _
    calc
      _ = |p.mass z.1 * ((productLaw p n).mass z.2 - (productLaw q n).mass z.2) +
          (p.mass z.1 - q.mass z.1) * (productLaw q n).mass z.2| := by congr 1; ring
      _ ≤ _ := by
        simpa only [abs_mul, abs_of_nonneg (p.nonneg z.1),
          abs_of_nonneg ((productLaw q n).nonneg z.2)] using
          abs_add_le (p.mass z.1 * ((productLaw p n).mass z.2 - (productLaw q n).mass z.2))
            ((p.mass z.1 - q.mass z.1) * (productLaw q n).mass z.2)
  have h := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hb z)
  refine h.trans_eq ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, (productLaw q n).total,
    mul_one, ← Finset.sum_mul, p.total, one_mul]

theorem totalVariation_productLaw_le (p q : Probability Ω) (n : ℕ) :
    totalVariation (productLaw p n) (productLaw q n) ≤ (n : ℝ) * totalVariation p q := by
  induction n with
  | zero => simp [totalVariation, productLaw]
  | succ n ih =>
    have h := productLaw_l1_succ_le p q n
    unfold totalVariation at *
    push_cast
    nlinarith

end IdentityTesting.FiniteTesting
