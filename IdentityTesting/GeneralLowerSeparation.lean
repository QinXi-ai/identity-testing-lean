import IdentityTesting.FinitePadding
import IdentityTesting.EmpiricalSeedLowerBound
import IdentityTesting.GeneralLowerGeometry

/-! Exact overlap bookkeeping for the actual all-radius lower-bound priors. -/

noncomputable section
namespace IdentityTesting.GeneralLowerGeometry
open scoped BigOperators
open Classical
open FiniteTesting EmpiricalSeeds

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- A perturbation supported on H spends exactly its total-variation distance
from the reference overlap on H. -/
theorem overlap_on_changed_set (p q : Probability Ω) (H : Finset Ω)
    (hout : ∀ i ∉ H, p.mass i = q.mass i) :
    (∑ i ∈ H, min (p.mass i) (q.mass i)) =
      (∑ i ∈ H, q.mass i) - FiniteTesting.totalVariation p q := by
  have htotal := Finset.sum_add_sum_compl H (fun i => min (p.mass i) (q.mass i))
  have hmass := (Finset.sum_add_sum_compl H q.mass).trans q.total
  have hcomp : (∑ i ∈ Hᶜ, min (p.mass i) (q.mass i)) = ∑ i ∈ Hᶜ, q.mass i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hout i (Finset.mem_compl.mp hi), min_self]
  rw [hcomp] at htotal
  rw [finite_totalVariation_eq_one_sub_overlap]
  linarith

theorem padded_totalVariation_eq_one_sub_overlap {k : ℕ}
    (p : Probability (Fin (k + 1))) (q : Probability (Fin k)) :
    FiniteTesting.totalVariation p (padFiniteLaw q) =
      1 - ∑ i : Fin k, min (p.mass i.castSucc) (q.mass i) := by
  rw [finite_totalVariation_eq_one_sub_overlap, Fin.sum_univ_castSucc]
  simp only [padFiniteLaw_mass_castSucc, padFiniteLaw_mass_last,
    min_eq_right (p.nonneg (Fin.last k)), add_zero]

/-- Positive margin gives strict separation at the original radius, including
empty H and all mass sent to the zero-reference label. -/
theorem compressed_alternative_separated {k : ℕ}
    (q : Probability (Fin k)) (x : Fin k → ℝ) (ε O : ℝ)
    (hε : (∑ i, q.mass i * x i) = ε) (p : Probability (Fin (k + 1)))
    (hlow : (∑ i ∈ lowCoords x, min (p.mass i.castSucc) (q.mass i)) ≤
      (∑ i ∈ lowCoords x, q.mass i) - 2 * lowDisplacement q.mass x)
    (hhigh : (∑ i ∈ highCoords x, min (p.mass i.castSucc) (q.mass i)) ≤ O)
    (hO : O < separationMargin q.mass x) :
    ε < FiniteTesting.totalVariation p (padFiniteLaw q) := by
  rw [padded_totalVariation_eq_one_sub_overlap]
  have hsplit := Finset.sum_add_sum_compl (lowCoords x)
    (fun i => min (p.mass i.castSucc) (q.mass i))
  have hmass := (Finset.sum_add_sum_compl (lowCoords x) q.mass).trans q.total
  have hradius := radius_partition q.mass x
  rw [hε] at hradius
  change _ + (∑ i ∈ highCoords x, min (p.mass i.castSucc) (q.mass i)) = _ at hsplit
  change _ + (∑ i ∈ highCoords x, q.mass i) = 1 at hmass
  dsimp only [separationMargin] at hO
  linarith

end IdentityTesting.GeneralLowerGeometry
