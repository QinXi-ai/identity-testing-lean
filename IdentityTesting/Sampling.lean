import IdentityTesting.CountableModel
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open scoped BigOperators
namespace IdentityTesting

set_option maxHeartbeats 800000 in
theorem hasSum_fin_prod {p : ℕ → ℝ} (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp : HasSum p 1) : ∀ n : ℕ,
    HasSum (fun x : Fin n → ℕ => ∏ i, p (x i)) 1 := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h_nonneg : 0 ≤ (fun x : Fin n → ℕ => ∏ i, p (x i)) := by
        intro x
        exact Finset.prod_nonneg (fun i _ => hp_nonneg (x i))
      have hsum : Summable (fun z : ℕ × (Fin n → ℕ) =>
          p z.1 * ∏ i, p (z.2 i)) :=
        Summable.mul_of_nonneg (f := p) (g := fun x : Fin n → ℕ => ∏ i, p (x i))
          hp.summable ih.summable hp_nonneg h_nonneg
      have h_prod : HasSum (fun z : ℕ × (Fin n → ℕ) =>
          p z.1 * ∏ i, p (z.2 i)) ((1 : ℝ) * 1) :=
        HasSum.mul (f := p) (g := fun x : Fin n → ℕ => ∏ i, p (x i)) hp ih hsum
      let f : (Fin (n + 1) → ℕ) → ℝ := fun x => ∏ i, p (x i)
      let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
      have hcomp : f ∘ e = (fun z : ℕ × (Fin n → ℕ) => p z.1 * ∏ i, p (z.2 i)) := by
        funext z
        simp only [Function.comp_apply, f, e, Fin.consEquiv_apply,
          Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hcons : HasSum (f ∘ e) 1 := by
        rw [hcomp]
        simpa only [one_mul] using h_prod
      exact (e.hasSum_iff (f := f) (a := 1)).mp hcons

theorem sampleMass_nonneg (p : DiscreteLaw) (n : ℕ) (x : Sample n) :
    0 ≤ sampleMass p n x := Finset.prod_nonneg (fun i _ => p.nonneg (x i))

theorem sampleMass_hasSum (p : DiscreteLaw) (n : ℕ) : HasSum (sampleMass p n) 1 := by
  have hp : HasSum p.mass 1 := by simpa only [p.total] using p.summable.hasSum
  simpa only [sampleMass, Sample] using hasSum_fin_prod p.nonneg hp n

theorem rejection_summable (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    Summable (fun x => sampleMass p n x * test.reject x) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (sampleMass_nonneg p n x) (test.nonneg x))
    (fun x => ?_) (sampleMass_hasSum p n).summable
  exact mul_le_of_le_one_right (sampleMass_nonneg p n x) (test.le_one x)

theorem acceptance_summable (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    Summable (fun x => sampleMass p n x * (1 - test.reject x)) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (sampleMass_nonneg p n x) (sub_nonneg.mpr (test.le_one x)))
    (fun x => ?_) (sampleMass_hasSum p n).summable
  exact mul_le_of_le_one_right (sampleMass_nonneg p n x) (by linarith [test.nonneg x])

theorem rejection_add_acceptance (p : DiscreteLaw) {n : ℕ} (test : RandomizedTest n) :
    rejectionProbability p test + acceptanceProbability p test = 1 := by
  unfold rejectionProbability acceptanceProbability
  rw [← (rejection_summable p test).tsum_add (acceptance_summable p test)]
  have h : (fun x => sampleMass p n x * test.reject x +
      sampleMass p n x * (1 - test.reject x)) = sampleMass p n := by
    funext x
    ring
  rw [h]
  exact (sampleMass_hasSum p n).tsum_eq

end IdentityTesting
