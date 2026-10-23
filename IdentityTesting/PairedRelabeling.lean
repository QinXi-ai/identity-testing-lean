import IdentityTesting.PairedPerturbation
import IdentityTesting.FiniteSampleMaps

/-!
# Relabeling the actual paired perturbation family

An arbitrary finite equivalence sends the block-encoded pairs to the original
reference labels.  The reference is pulled back with the actual `mapLaw`; the
constructed paired alternatives are then pushed forward.  Positivity, TV, and
likelihood identities are derived from these actual maps.  The final obstruction
is for the original reference `q`, not merely its block-coordinate copy.

Selecting an equivalence that realizes the manuscript's chosen/sorted pairs and
proving its scalar amplitude/allocation bounds remain caller obligations.
-/

noncomputable section
open scoped BigOperators

namespace IdentityTesting.PairedRelabeling

open PairedPerturbation SignedDiagonalMoment

universe u v

variable {Ω : Type u} {Ξ : Type v} [Fintype Ω] [Fintype Ξ]

@[simp] theorem mapLaw_equiv_mass (p : FiniteTesting.Probability Ω) (e : Ω ≃ Ξ) (y : Ξ) :
    (FiniteTesting.mapLaw p e).mass y = p.mass (e.symm y) := by
  classical
  have hiff : ∀ x, e x = y ↔ x = e.symm y := by
    intro x
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply y).symm)
    · intro h
      rw [h, e.apply_symm_apply]
  rw [FiniteTesting.mapLaw_mass]
  simp only [hiff]
  simp

theorem mapLaw_equiv_positive (p : FiniteTesting.Probability Ω) (e : Ω ≃ Ξ)
    (hp : ∀ x, 0 < p.mass x) : ∀ y, 0 < (FiniteTesting.mapLaw p e).mass y := by
  intro y
  rw [mapLaw_equiv_mass]
  exact hp _

theorem mapLaw_equiv_roundtrip (q : FiniteTesting.Probability Ξ) (e : Ω ≃ Ξ) :
    FiniteTesting.mapLaw (FiniteTesting.mapLaw q e.symm) e = q := by
  apply FiniteTesting.probability_ext
  intro y
  simp only [mapLaw_equiv_mass, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem mapLaw_equiv_totalVariation (p q : FiniteTesting.Probability Ω) (e : Ω ≃ Ξ) :
    FiniteTesting.totalVariation (FiniteTesting.mapLaw p e) (FiniteTesting.mapLaw q e) =
      FiniteTesting.totalVariation p q := by
  unfold FiniteTesting.totalVariation
  simp only [mapLaw_equiv_mass]
  congr 1
  exact e.symm.sum_comp (fun x => |p.mass x - q.mass x|)

theorem mapLaw_equiv_likelihoodInner (p r q : FiniteTesting.Probability Ω) (e : Ω ≃ Ξ) :
    FiniteChiSquare.likelihoodInner (FiniteTesting.mapLaw p e) (FiniteTesting.mapLaw r e)
      (FiniteTesting.mapLaw q e) = FiniteChiSquare.likelihoodInner p r q := by
  unfold FiniteChiSquare.likelihoodInner
  simp only [mapLaw_equiv_mass]
  exact e.symm.sum_comp (fun x => p.mass x * r.mass x / q.mass x)

variable {d t k : ℕ}

def pullbackReference (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) :
    FiniteTesting.Probability (Fin (d + (d + t))) :=
  FiniteTesting.mapLaw q e.symm

@[simp] theorem pullbackReference_mass (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (x : Fin (d + (d + t))) :
    (pullbackReference q e).mass x = q.mass (e x) := by
  simp only [pullbackReference, mapLaw_equiv_mass, Equiv.symm_symm]

theorem pullbackReference_positive (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (hq : ∀ x, 0 < q.mass x) :
    ∀ x, 0 < (pullbackReference q e).mass x := by
  intro x
  rw [pullbackReference_mass]
  exact hq _

private theorem pullback_amplitude_bounds (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j))) :
    ∀ j, 0 ≤ a j ∧ a j ≤ (pullbackReference q e).mass (leftIndex j) ∧
      a j ≤ (pullbackReference q e).mass (rightIndex j) := by
  intro j
  simpa only [pullbackReference_mass] using ha j

/-- The actual normalized paired family on the original `Fin k` labels. -/
def relabeledPairedLaw (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j)))
    (σ : Fin d → Bool) : FiniteTesting.Probability (Fin k) :=
  FiniteTesting.mapLaw
    (pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ) e

@[simp] theorem relabeledPairedLaw_mass_apply (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j)))
    (σ : Fin d → Bool) (x : Fin (d + (d + t))) :
    (relabeledPairedLaw q e a ha σ).mass (e x) =
      (pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ).mass x := by
  simp only [relabeledPairedLaw, mapLaw_equiv_mass, Equiv.symm_apply_apply]

/-- The complete IID sample law is also the actual coordinatewise pushforward. -/
theorem relabeledPairedLaw_productLaw (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j)))
    (σ : Fin d → Bool) (n : ℕ) :
    FiniteTesting.productLaw (relabeledPairedLaw q e a ha σ) n =
      FiniteTesting.mapLaw
        (FiniteTesting.productLaw
          (pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ) n)
        (fun sample => e ∘ sample) := by
  exact (FiniteTesting.mapLaw_productLaw _ e n).symm

theorem relabeledPairedLaw_totalVariation (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j))) (σ : Fin d → Bool) :
    FiniteTesting.totalVariation (relabeledPairedLaw q e a ha σ) q = ∑ j, a j := by
  have hround : FiniteTesting.mapLaw (pullbackReference q e) e = q :=
    mapLaw_equiv_roundtrip q e
  let p := pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ
  change FiniteTesting.totalVariation (FiniteTesting.mapLaw p e) q = _
  calc
    FiniteTesting.totalVariation (FiniteTesting.mapLaw p e) q =
        FiniteTesting.totalVariation (FiniteTesting.mapLaw p e)
          (FiniteTesting.mapLaw (pullbackReference q e) e) :=
      congrArg (fun r => FiniteTesting.totalVariation (FiniteTesting.mapLaw p e) r) hround.symm
    _ = FiniteTesting.totalVariation p (pullbackReference q e) :=
      mapLaw_equiv_totalVariation p (pullbackReference q e) e
    _ = ∑ j, a j :=
      pairedLaw_totalVariation (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ

def relabeledCoefficient (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ) (j : Fin d) : ℝ :=
  a j ^ 2 * (1 / q.mass (e (leftIndex j)) + 1 / q.mass (e (rightIndex j)))

theorem pairedCoefficient_pullbackReference (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ) :
    pairedCoefficient (pullbackReference q e) a = relabeledCoefficient q e a := by
  funext j
  simp only [pairedCoefficient, relabeledCoefficient, pullbackReference_mass]

theorem relabeledPairedLaw_likelihoodInner (q : FiniteTesting.Probability (Fin k))
    (e : Fin (d + (d + t)) ≃ Fin k) (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j)))
    (hq : ∀ x, 0 < q.mass x) (σ τ : Fin d → Bool) :
    FiniteChiSquare.likelihoodInner (relabeledPairedLaw q e a ha σ)
      (relabeledPairedLaw q e a ha τ) q =
        1 + diagonalInteraction (relabeledCoefficient q e a) σ τ := by
  have hround : FiniteTesting.mapLaw (pullbackReference q e) e = q :=
    mapLaw_equiv_roundtrip q e
  let pσ := pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) σ
  let pτ := pairedLaw (pullbackReference q e) a (pullback_amplitude_bounds q e a ha) τ
  change FiniteChiSquare.likelihoodInner (FiniteTesting.mapLaw pσ e)
    (FiniteTesting.mapLaw pτ e) q = _
  calc
    FiniteChiSquare.likelihoodInner (FiniteTesting.mapLaw pσ e) (FiniteTesting.mapLaw pτ e) q =
        FiniteChiSquare.likelihoodInner (FiniteTesting.mapLaw pσ e) (FiniteTesting.mapLaw pτ e)
          (FiniteTesting.mapLaw (pullbackReference q e) e) :=
      congrArg (fun r => FiniteChiSquare.likelihoodInner (FiniteTesting.mapLaw pσ e)
        (FiniteTesting.mapLaw pτ e) r) hround.symm
    _ = FiniteChiSquare.likelihoodInner pσ pτ (pullbackReference q e) :=
      mapLaw_equiv_likelihoodInner pσ pτ (pullbackReference q e) e
    _ = _ := by
      dsimp only [pσ, pτ]
      rw [pairedLaw_likelihoodInner _ _ _ (pullbackReference_positive q e hq),
        pairedCoefficient_pullbackReference]

/-- The actual relabeled paired prior excludes tests at the original reference `q`. -/
theorem no_identityTest_of_relabeled_paired_perturbation
    (q : FiniteTesting.Probability (Fin k)) (e : Fin (d + (d + t)) ≃ Fin k)
    (a : Fin d → ℝ)
    (ha : ∀ j, 0 ≤ a j ∧ a j ≤ q.mass (e (leftIndex j)) ∧
      a j ≤ q.mass (e (rightIndex j)))
    (hq : ∀ x, 0 < q.mass x) (ε : ℝ) (n : ℕ)
    (hseparated : ε < ∑ j, a j)
    (hsmall : Real.exp ((n : ℝ) ^ 2 / 2 * ∑ j, relabeledCoefficient q e a j ^ 2) <
      (13 : ℝ) / 9) :
    ¬ HasIdentityTest (extendFiniteLaw q) ε n := by
  apply no_identityTest_extendFiniteLaw_of_diagonal_likelihood
    (relabeledPairedLaw q e a ha) q (relabeledCoefficient q e a) ε n hq
    (relabeledPairedLaw_likelihoodInner q e a ha hq)
  · intro σ
    rw [relabeledPairedLaw_totalVariation]
    exact hseparated
  · exact hsmall

end IdentityTesting.PairedRelabeling
