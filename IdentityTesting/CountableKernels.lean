import IdentityTesting.Sampling
import IdentityTesting.FiniteTesting

/-! Actual stochastic kernels from a finite alphabet to the countable alphabet,
including their independent action on n observations and randomized tests. -/

noncomputable section
open scoped BigOperators
namespace IdentityTesting
open FiniteTesting

@[ext] theorem DiscreteLaw.ext {p q : DiscreteLaw}
    (h : ∀ i, p.mass i = q.mass i) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

variable {Ω : Type*} [Fintype Ω]

def countableMixture (p : Probability Ω) (K : Ω → DiscreteLaw) : DiscreteLaw where
  mass i := ∑ x, p.mass x * (K x).mass i
  nonneg i := Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) ((K x).nonneg i))
  summable := summable_sum (fun x _ => (K x).summable.mul_left (p.mass x))
  total := by
    rw [Summable.tsum_finsetSum (fun x _ => (K x).summable.mul_left (p.mass x))]
    simp only [tsum_mul_left, DiscreteLaw.total, mul_one]
    exact p.total

def kernelSampleMass (K : Ω → DiscreteLaw) {n : ℕ} (y : Fin n → Ω) (x : Sample n) : ℝ :=
  ∏ j, (K (y j)).mass (x j)

omit [Fintype Ω] in
theorem kernelSampleMass_nonneg (K : Ω → DiscreteLaw) {n : ℕ}
    (y : Fin n → Ω) (x : Sample n) : 0 ≤ kernelSampleMass K y x :=
  Finset.prod_nonneg (fun j _ => (K (y j)).nonneg (x j))

set_option maxHeartbeats 800000 in
omit [Fintype Ω] in
theorem kernelSampleMass_hasSum (K : Ω → DiscreteLaw) : ∀ (n : ℕ) (y : Fin n → Ω),
    HasSum (kernelSampleMass K y) 1 := by
  intro n
  induction n with
  | zero =>
    intro y
    change HasSum (fun x : Fin 0 → ℕ => ∏ j : Fin 0, (K (y j)).mass (x j)) 1
    simp
  | succ n ih =>
    intro y
    have htail := ih (fun j => y j.succ)
    have hzero : HasSum (K (y 0)).mass 1 := by
      simpa only [DiscreteLaw.total] using (K (y 0)).summable.hasSum
    have hprod := HasSum.mul hzero htail
      (Summable.mul_of_nonneg hzero.summable htail.summable
        (K (y 0)).nonneg (kernelSampleMass_nonneg K _))
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) :=
      Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
    have hcomp : kernelSampleMass K y ∘ e =
        (fun z : ℕ × (Fin n → ℕ) =>
          (K (y 0)).mass z.1 * kernelSampleMass K (fun j => y j.succ) z.2) := by
      funext z
      simp only [Function.comp_apply, kernelSampleMass, e, Fin.consEquiv_apply,
        Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hcons : HasSum (kernelSampleMass K y ∘ e) 1 := by
      rw [hcomp]
      simpa only [one_mul] using hprod
    exact (e.hasSum_iff).mp hcons

omit [Fintype Ω] in
theorem kernel_rejection_summable (K : Ω → DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) (y : Fin n → Ω) :
    Summable (fun x => kernelSampleMass K y x * test.reject x) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (kernelSampleMass_nonneg K y x) (test.nonneg x))
    (fun x => mul_le_of_le_one_right (kernelSampleMass_nonneg K y x) (test.le_one x))
    (kernelSampleMass_hasSum K n y).summable

def kernelAverageTest (K : Ω → DiscreteLaw) {n : ℕ}
    (test : IdentityTesting.RandomizedTest n) :
    FiniteTesting.RandomizedTest (Fin n → Ω) where
  reject y := ∑' x, kernelSampleMass K y x * test.reject x
  nonneg y := tsum_nonneg (fun x => mul_nonneg (kernelSampleMass_nonneg K y x) (test.nonneg x))
  le_one y := by
    have h := (kernel_rejection_summable K test y).tsum_le_tsum
      (fun x => mul_le_of_le_one_right (kernelSampleMass_nonneg K y x) (test.le_one x))
      (kernelSampleMass_hasSum K n y).summable
    exact h.trans_eq (kernelSampleMass_hasSum K n y).tsum_eq

theorem sampleMass_countableMixture (p : Probability Ω) (K : Ω → DiscreteLaw)
    (n : ℕ) (x : Sample n) :
    sampleMass (countableMixture p K) n x =
      ∑ y : Fin n → Ω, (productLaw p n).mass y * kernelSampleMass K y x := by
  change (∏ j, ∑ i, p.mass i * (K i).mass (x j)) = _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.prod_mul_distrib

theorem rejectionProbability_countableMixture (p : Probability Ω) (K : Ω → DiscreteLaw)
    {n : ℕ} (test : IdentityTesting.RandomizedTest n) :
    rejectionProbability (countableMixture p K) test =
      expectation (productLaw p n) (kernelAverageTest K test) := by
  unfold rejectionProbability
  simp_rw [sampleMass_countableMixture, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun y _ =>
    (kernel_rejection_summable K test y).mul_left ((productLaw p n).mass y))]
  unfold expectation kernelAverageTest
  apply Finset.sum_congr rfl
  intro y _
  simp only [tsum_mul_left]

theorem acceptanceProbability_countableMixture (p : Probability Ω) (K : Ω → DiscreteLaw)
    {n : ℕ} (test : IdentityTesting.RandomizedTest n) :
    acceptanceProbability (countableMixture p K) test =
      1 - expectation (productLaw p n) (kernelAverageTest K test) := by
  have h := rejection_add_acceptance (countableMixture p K) test
  rw [rejectionProbability_countableMixture] at h
  linarith

end IdentityTesting
