import IdentityTesting.SignedDiagonalMoment
import Mathlib.Tactic.FieldSimp

/-!
# Actual disjoint-pair signed perturbations

The finite reference has three blocks: `d` left endpoints, `d` right endpoints,
and `u` untouched coordinates.  A sign moves an amplitude between the two
endpoints of its pair.  The resulting laws are constructed and normalized here;
their exact TV and diagonal likelihood identity are derived, not supplied.

The final lower bound retains only the elementwise amplitude constraints,
strict separation of the amplitude sum, and a scalar exponential moment bound.
The manuscript's allocation estimates that imply these scalar bounds are not
asserted by this module.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.PairedPerturbation

open SignedDiagonalMoment

variable {d u : ℕ}

def leftIndex (j : Fin d) : Fin (d + (d + u)) := Fin.castAdd (d + u) j

def rightIndex (j : Fin d) : Fin (d + (d + u)) := Fin.natAdd d (Fin.castAdd u j)

def untouchedIndex (i : Fin u) : Fin (d + (d + u)) := Fin.natAdd d (Fin.natAdd d i)

private theorem sum_split (f : Fin (d + (d + u)) → ℝ) :
    (∑ i, f i) = (∑ j : Fin d, f (leftIndex j)) +
      ((∑ j : Fin d, f (rightIndex j)) + ∑ i : Fin u, f (untouchedIndex i)) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  rfl

def pairedMass (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (σ : Fin d → Bool) : Fin (d + (d + u)) → ℝ :=
  Fin.append
    (fun j => q.mass (leftIndex j) + a j * sign (σ j))
    (Fin.append
      (fun j => q.mass (rightIndex j) - a j * sign (σ j))
      (fun i : Fin u => q.mass (untouchedIndex i)))

@[simp] theorem pairedMass_left (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (σ : Fin d → Bool) (j : Fin d) :
    pairedMass q a σ (leftIndex j) = q.mass (leftIndex j) + a j * sign (σ j) := by
  simp [pairedMass, leftIndex]

@[simp] theorem pairedMass_right (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (σ : Fin d → Bool) (j : Fin d) :
    pairedMass q a σ (rightIndex j) = q.mass (rightIndex j) - a j * sign (σ j) := by
  simp [pairedMass, rightIndex]

@[simp] theorem pairedMass_untouched (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (σ : Fin d → Bool) (i : Fin u) :
    pairedMass q a σ (untouchedIndex i) = q.mass (untouchedIndex i) := by
  simp [pairedMass, untouchedIndex]

private theorem plus_sign_nonneg (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (har : a ≤ r)
    (b : Bool) : 0 ≤ r + a * sign b := by
  cases b <;> simp only [sign, mul_one, mul_neg_one] <;> linarith only [hr, ha, har]

private theorem minus_sign_nonneg (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (har : a ≤ r)
    (b : Bool) : 0 ≤ r - a * sign b := by
  cases b <;> simp only [sign, mul_one, mul_neg_one] <;> linarith only [hr, ha, har]

theorem pairedMass_nonneg (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) (i : Fin (d + (d + u))) : 0 ≤ pairedMass q a σ i := by
  refine Fin.addCases (fun j => ?_) (fun rest => ?_) i
  · change 0 ≤ pairedMass q a σ (leftIndex j)
    rw [pairedMass_left]
    exact plus_sign_nonneg _ _ (q.nonneg _) (ha j).1 (ha j).2.1 (σ j)
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) rest
    · change 0 ≤ pairedMass q a σ (rightIndex j)
      rw [pairedMass_right]
      exact minus_sign_nonneg _ _ (q.nonneg _) (ha j).1 (ha j).2.2 (σ j)
    · change 0 ≤ pairedMass q a σ (untouchedIndex l)
      rw [pairedMass_untouched]
      exact q.nonneg _

theorem pairedMass_total (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (σ : Fin d → Bool) : ∑ i, pairedMass q a σ i = 1 := by
  have hq := q.total
  rw [sum_split] at hq
  rw [sum_split]
  simp only [pairedMass_left, pairedMass_right, pairedMass_untouched,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith only [hq]

/-- The actual normalized signed family; its constraints are only amplitude bounds. -/
def pairedLaw (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) : FiniteTesting.Probability (Fin (d + (d + u))) where
  mass := pairedMass q a σ
  nonneg := pairedMass_nonneg q a ha σ
  total := pairedMass_total q a σ

@[simp] theorem pairedLaw_mass_left (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) (j : Fin d) :
    (pairedLaw q a ha σ).mass (leftIndex j) = q.mass (leftIndex j) + a j * sign (σ j) :=
  pairedMass_left q a σ j

@[simp] theorem pairedLaw_mass_right (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) (j : Fin d) :
    (pairedLaw q a ha σ).mass (rightIndex j) = q.mass (rightIndex j) - a j * sign (σ j) :=
  pairedMass_right q a σ j

@[simp] theorem pairedLaw_mass_untouched (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) (i : Fin u) :
    (pairedLaw q a ha σ).mass (untouchedIndex i) = q.mass (untouchedIndex i) :=
  pairedMass_untouched q a σ i

private theorem abs_sign_mul (a : ℝ) (ha : 0 ≤ a) (b : Bool) : |a * sign b| = a := by
  cases b <;> simp [sign, abs_of_nonneg ha]

/-- Each pair contributes exactly its amplitude to total variation. -/
theorem pairedLaw_totalVariation (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (σ : Fin d → Bool) :
    FiniteTesting.totalVariation (pairedLaw q a ha σ) q = ∑ j, a j := by
  have hleft : ∀ j,
      |q.mass (leftIndex j) + a j * sign (σ j) - q.mass (leftIndex j)| = a j := by
    intro j
    calc
      _ = |a j * sign (σ j)| := by congr 1; ring
      _ = a j := abs_sign_mul _ (ha j).1 _
  have hright : ∀ j,
      |q.mass (rightIndex j) - a j * sign (σ j) - q.mass (rightIndex j)| = a j := by
    intro j
    calc
      _ = |-(a j * sign (σ j))| := by congr 1; ring
      _ = |a j * sign (σ j)| := abs_neg _
      _ = a j := abs_sign_mul _ (ha j).1 _
  unfold FiniteTesting.totalVariation
  rw [sum_split]
  simp only [pairedLaw_mass_left, pairedLaw_mass_right, pairedLaw_mass_untouched,
    hleft, hright, sub_self, abs_zero, Finset.sum_const_zero, add_zero]
  ring

def pairedCoefficient (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ) (j : Fin d) : ℝ :=
  a j ^ 2 * (1 / q.mass (leftIndex j) + 1 / q.mass (rightIndex j))

private theorem paired_likelihood_scalar (l r a b c : ℝ) (hl : l ≠ 0) (hr : r ≠ 0) :
    (l + a * b) * (l + a * c) / l + (r - a * b) * (r - a * c) / r =
      l + r + a ^ 2 * (1 / l + 1 / r) * b * c := by
  field_simp [hl, hr]
  ring

/-- The diagonal likelihood identity follows from the constructed perturbations. -/
theorem pairedLaw_likelihoodInner (q : FiniteTesting.Probability (Fin (d + (d + u))))
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (hq : ∀ i, 0 < q.mass i) (σ τ : Fin d → Bool) :
    FiniteChiSquare.likelihoodInner (pairedLaw q a ha σ) (pairedLaw q a ha τ) q =
      1 + diagonalInteraction (pairedCoefficient q a) σ τ := by
  let L : Fin d → ℝ := fun j =>
    (q.mass (leftIndex j) + a j * sign (σ j)) *
      (q.mass (leftIndex j) + a j * sign (τ j)) / q.mass (leftIndex j)
  let R : Fin d → ℝ := fun j =>
    (q.mass (rightIndex j) - a j * sign (σ j)) *
      (q.mass (rightIndex j) - a j * sign (τ j)) / q.mass (rightIndex j)
  have hpair : ∀ j, L j + R j = q.mass (leftIndex j) + q.mass (rightIndex j) +
      pairedCoefficient q a j * sign (σ j) * sign (τ j) := by
    intro j
    exact paired_likelihood_scalar _ _ _ _ _
      (ne_of_gt (hq (leftIndex j))) (ne_of_gt (hq (rightIndex j)))
  have huntouched :
      (∑ i : Fin u, q.mass (untouchedIndex i) * q.mass (untouchedIndex i) /
        q.mass (untouchedIndex i)) = ∑ i : Fin u, q.mass (untouchedIndex i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_cancel_right₀ _ (ne_of_gt (hq (untouchedIndex i)))
  have hqtotal := q.total
  rw [sum_split] at hqtotal
  unfold FiniteChiSquare.likelihoodInner diagonalInteraction
  rw [sum_split]
  simp only [pairedLaw_mass_left, pairedLaw_mass_right, pairedLaw_mass_untouched]
  change (∑ j, L j) + ((∑ j, R j) +
    (∑ i : Fin u, q.mass (untouchedIndex i) * q.mass (untouchedIndex i) /
      q.mass (untouchedIndex i))) =
    1 + ∑ j, pairedCoefficient q a j * sign (σ j) * sign (τ j)
  rw [huntouched]
  calc
    (∑ j, L j) + ((∑ j, R j) + ∑ i : Fin u, q.mass (untouchedIndex i)) =
        (∑ j, (L j + R j)) + ∑ i : Fin u, q.mass (untouchedIndex i) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = (∑ j, (q.mass (leftIndex j) + q.mass (rightIndex j) +
        pairedCoefficient q a j * sign (σ j) * sign (τ j))) +
        ∑ i : Fin u, q.mass (untouchedIndex i) := by
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hpair j)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      linarith only [hqtotal]

theorem chiSquare_paired_iid_mixture_le
    (q : FiniteTesting.Probability (Fin (d + (d + u)))) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (hq : ∀ i, 0 < q.mass i) (n : ℕ) :
    FiniteChiSquare.chiSquare
      (FiniteTesting.mixture (uniformSigns d)
        (fun σ => FiniteTesting.productLaw (pairedLaw q a ha σ) n))
      (FiniteTesting.productLaw q n) ≤
        Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, pairedCoefficient q a j ^ 2) - 1 := by
  exact chiSquare_iid_mixture_le (pairedLaw q a ha) q (pairedCoefficient q a) n
    (pairedLaw_likelihoodInner q a ha hq)

/-- A fully constructed paired prior gives a lower bound in the original model.
No TV or likelihood identity is assumed; only amplitude and scalar size bounds remain. -/
theorem no_identityTest_of_paired_perturbation
    (q : FiniteTesting.Probability (Fin (d + (d + u)))) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (leftIndex j) ∧ a j ≤ q.mass (rightIndex j))
    (hq : ∀ i, 0 < q.mass i) (ε : ℝ) (n : ℕ)
    (hseparated : ε < ∑ j, a j)
    (hsmall : Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, pairedCoefficient q a j ^ 2) <
      (13 : ℝ) / 9) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  apply no_identityTest_extendFiniteLaw_of_diagonal_likelihood
    (pairedLaw q a ha) q (pairedCoefficient q a) ε n hq
    (pairedLaw_likelihoodInner q a ha hq)
  · intro σ
    rw [pairedLaw_totalVariation]
    exact hseparated
  · exact hsmall

end IdentityTesting.PairedPerturbation
