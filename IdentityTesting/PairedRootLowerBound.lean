import IdentityTesting.GeneralAllocationBounds
import IdentityTesting.PairedRelabeling

/-!
# The paired prior's numerical lower-bound caller

The small-sample exponential condition is proved from the allocation rate.
The remaining combinatorial input is a concrete pairing with small right
coordinates and a sufficiently large amplitude sum.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting

theorem paired_exp_rate_sub_one_lt {ι : Type*} [Fintype ι] (M : ι → ℝ)
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    (hM : (∑ i, M i ^ 2) ≤ 16384 / T ^ 2)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    Real.exp ((n : ℝ) ^ 2 / 2 * ∑ i, M i ^ 2) - 1 < 4 / (10 : ℝ) ^ 18 := by
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  have hz : (n : ℝ) ^ 2 / 2 * (∑ i, M i ^ 2) ≤ 1 / (10 : ℝ) ^ 20 := by
    calc
      _ ≤ (n : ℝ) ^ 2 / 2 * (16384 / T ^ 2) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 8192 * (n : ℝ) ^ 2 / T ^ 2 := by ring
      _ ≤ _ := by
        apply (div_le_iff₀ hT2).2
        norm_num at hn2 ⊢
        nlinarith only [hn2]
  have hexp := (Real.exp_le_exp.mpr hz).trans
    (Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 20) (by norm_num))
  have hnum : (1 : ℝ) / (1 - 1 / (10 : ℝ) ^ 20) - 1 < 4 / (10 : ℝ) ^ 18 := by norm_num
  linarith only [hexp, hnum]

theorem paired_exp_rate_lt {ι : Type*} [Fintype ι] (M : ι → ℝ)
    {T : ℝ} (hT : 0 < T) (n : ℕ)
    (hM : (∑ i, M i ^ 2) ≤ 16384 / T ^ 2)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    Real.exp ((n : ℝ) ^ 2 / 2 * ∑ i, M i ^ 2) < (13 : ℝ) / 9 := by
  have h := paired_exp_rate_sub_one_lt M hT n hM hn
  norm_num at h ⊢
  linarith only [h]

/-- The manuscript's quantitative sample-TV bound for an actual diagonal
signed family. This form is useful before applying a common sample kernel. -/
theorem diagonal_iid_mixture_totalVariation_lt_rate {Ω : Type*} [Fintype Ω] {d : ℕ}
    (family : (Fin d → Bool) → FiniteTesting.Probability Ω)
    (q : FiniteTesting.Probability Ω) (M : Fin d → ℝ) {T : ℝ}
    (hT : 0 < T) (n : ℕ) (hq : ∀ i, 0 < q.mass i)
    (hinner : ∀ σ τ, FiniteChiSquare.likelihoodInner (family σ) (family τ) q =
      1 + SignedDiagonalMoment.diagonalInteraction M σ τ)
    (hM : (∑ j, M j ^ 2) ≤ 16384 / T ^ 2)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    FiniteTesting.totalVariation
      (FiniteTesting.mixture (SignedDiagonalMoment.uniformSigns d)
        (fun σ => FiniteTesting.productLaw (family σ) n))
      (FiniteTesting.productLaw q n) < 1 / (10 : ℝ) ^ 9 := by
  let Q := FiniteTesting.mixture (SignedDiagonalMoment.uniformSigns d)
    (fun σ => FiniteTesting.productLaw (family σ) n)
  let qn := FiniteTesting.productLaw q n
  have hchi : FiniteChiSquare.chiSquare Q qn < 4 / (10 : ℝ) ^ 18 :=
    (SignedDiagonalMoment.chiSquare_iid_mixture_le family q M n hinner).trans_lt
      (paired_exp_rate_sub_one_lt M hT n hM hn)
  have hTV := FiniteChiSquare.totalVariation_sq_le_chiSquare_div_four Q qn
    (FiniteMomentLowerBound.productLaw_mass_pos q hq n)
  change FiniteTesting.totalVariation Q qn < 1 / (10 : ℝ) ^ 9
  by_contra hnot
  have hlarge : 1 / (10 : ℝ) ^ 9 ≤ FiniteTesting.totalVariation Q qn := le_of_not_gt hnot
  have hmul := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 9) hlarge
  norm_num at hchi hTV hmul
  nlinarith only [hchi, hTV, hmul]

theorem relabeled_paired_mixture_totalVariation_lt_rate {d t k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (e : Fin (d + (d + t)) ≃ Fin k)
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (PairedPerturbation.leftIndex j)) ∧
      a j ≤ q.mass (e (PairedPerturbation.rightIndex j)))
    {T : ℝ} (hT : 0 < T) (n : ℕ) (hq : ∀ i, 0 < q.mass i)
    (hM : (∑ j, (PairedRelabeling.relabeledCoefficient q e a j) ^ 2) ≤ 16384 / T ^ 2)
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    FiniteTesting.totalVariation
      (FiniteTesting.mixture (SignedDiagonalMoment.uniformSigns d)
        (fun σ => FiniteTesting.productLaw (PairedRelabeling.relabeledPairedLaw q e a ha σ) n))
      (FiniteTesting.productLaw q n) < 1 / (10 : ℝ) ^ 9 := by
  exact diagonal_iid_mixture_totalVariation_lt_rate
    (PairedRelabeling.relabeledPairedLaw q e a ha) q
    (PairedRelabeling.relabeledCoefficient q e a) hT n hq
    (PairedRelabeling.relabeledPairedLaw_likelihoodInner q e a ha hq) hM hn

theorem allocation_pair_amplitude_bounds {l r x : ℝ}
    (hr : 0 ≤ r) (hrl : r ≤ l) (hx : 0 ≤ x) (hxsmall : x ≤ (1 : ℝ) / 8) :
    0 ≤ 8 * r * x ∧ 8 * r * x ≤ l ∧ 8 * r * x ≤ r := by
  have hbound := mul_le_mul_of_nonneg_left hxsmall hr
  have hright : 8 * r * x ≤ r := by nlinarith only [hbound]
  exact ⟨by positivity, hright.trans hrl, hright⟩

theorem relabeledCoefficient_allocation_bound {d t k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (e : Fin (d + (d + t)) ≃ Fin k)
    (x : Fin k → ℝ) {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q.mass i)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (horder : ∀ j, q.mass (e (PairedPerturbation.rightIndex j)) ≤
      q.mass (e (PairedPerturbation.leftIndex j)))
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1) :
    (∑ j, (PairedRelabeling.relabeledCoefficient q e
      (fun j => 8 * q.mass (e (PairedPerturbation.rightIndex j)) *
        x (e (PairedPerturbation.rightIndex j))) j) ^ 2) ≤ 16384 / T ^ 2 := by
  apply allocation_paired_coefficient_bound q.mass x
    (e ∘ PairedPerturbation.leftIndex) (e ∘ PairedPerturbation.rightIndex) ?_
    hT hq hx horder hbudget
  intro a b hab
  have h := e.injective hab
  apply Fin.ext
  have hh := congrArg Fin.val h
  change d + a.val = d + b.val at hh
  exact Nat.add_left_cancel hh

/-- This caller proves amplitude legality and the exponential condition and
then invokes the actual relabeled paired family in the original testing model. -/
theorem no_identityTest_of_relabeled_allocation_pairing {d t k : ℕ}
    (q : FiniteTesting.Probability (Fin k)) (e : Fin (d + (d + t)) ≃ Fin k)
    (x : Fin k → ℝ) {T : ℝ} (hT : 0 < T) (hq : ∀ i, 0 < q.mass i)
    (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (horder : ∀ j, q.mass (e (PairedPerturbation.rightIndex j)) ≤
      q.mass (e (PairedPerturbation.leftIndex j)))
    (hsmall : ∀ j, x (e (PairedPerturbation.rightIndex j)) ≤ (1 : ℝ) / 8)
    (hbudget : T ^ 2 * (∑ i, (q.mass i) ^ 2 * (x i) ^ 4 / (1 - (x i) ^ 4)) = 1)
    (ε : ℝ) (n : ℕ)
    (hseparated : ε < ∑ j, 8 * q.mass (e (PairedPerturbation.rightIndex j)) *
      x (e (PairedPerturbation.rightIndex j)))
    (hn : (n : ℝ) ≤ (1 / (10 : ℝ) ^ 12) * T) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  let a : Fin d → ℝ := fun j => 8 * q.mass (e (PairedPerturbation.rightIndex j)) *
    x (e (PairedPerturbation.rightIndex j))
  have ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (PairedPerturbation.leftIndex j)) ∧
      a j ≤ q.mass (e (PairedPerturbation.rightIndex j)) := by
    intro j
    exact allocation_pair_amplitude_bounds (hq _).le (horder j) (hx _).1 (hsmall j)
  apply PairedRelabeling.no_identityTest_of_relabeled_paired_perturbation
    q e a ha hq ε n hseparated
  exact paired_exp_rate_lt _ hT n
    (relabeledCoefficient_allocation_bound q e x hT hq hx horder hbudget) hn

end IdentityTesting
