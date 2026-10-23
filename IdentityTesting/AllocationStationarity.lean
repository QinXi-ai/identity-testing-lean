import IdentityTesting.AllocationRegularity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Stationarity constructed from actual allocation optimizers

The coordinate derivative is obtained from the already proved inverse cost map.
Feasible pairwise mass transfers turn global optimizer maximality into a
one-dimensional local maximum, whose derivative vanishes by Fermat's theorem.
The resulting common positive marginal constructs the KKT scalar.
-/

namespace IdentityTesting

open scoped BigOperators Topology
open Filter

theorem allocationCoordinate_pos {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    0 < allocationCoordinate t a u := by
  simpa only [allocationCoordinate_zero] using
    allocationCoordinate_lt ht ha (le_refl (0 : ℝ)) hu

/-- Derivative of the concrete inverse budget cost. -/
theorem hasDerivAt_allocationCost {t a x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (allocationCost t a)
      (4 * t ^ 2 * a ^ 2 * x ^ 3 / (1 - x ^ 4) ^ 2) x := by
  have hden : 1 - x ^ 4 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hx0 hx1))
  have hn : HasDerivAt (fun y : ℝ => t ^ 2 * a ^ 2 * y ^ 4)
      (t ^ 2 * a ^ 2 * (4 * x ^ 3)) x := by
    simpa using ((hasDerivAt_id x).pow 4).const_mul (t ^ 2 * a ^ 2)
  have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 4) (-(4 * x ^ 3)) x := by
    simpa using (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 4)
  change HasDerivAt (fun y : ℝ => t ^ 2 * a ^ 2 * y ^ 4 / (1 - y ^ 4)) _ x
  apply (hn.div hd hden).congr_deriv
  ring

theorem allocationCost_derivative_pos {t a x : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hx0 : 0 < x) (hx1 : x < 1) :
    0 < 4 * t ^ 2 * a ^ 2 * x ^ 3 / (1 - x ^ 4) ^ 2 := by
  have hden : 0 < 1 - x ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  positivity

theorem continuousAt_allocationCoordinate {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    ContinuousAt (allocationCoordinate t a) u := by
  have hden : u + t ^ 2 * a ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hratio : ContinuousAt (fun y : ℝ => y / (y + t ^ 2 * a ^ 2)) u :=
    continuousAt_id.div (continuousAt_id.add continuousAt_const) hden
  simpa only [allocationCoordinate] using hratio.sqrt.sqrt

/-- The coordinate derivative is constructed using its actual local inverse,
not assumed as part of a stationarity certificate. -/
theorem hasDerivAt_allocationCoordinate {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    HasDerivAt (allocationCoordinate t a)
      (4 * t ^ 2 * a ^ 2 * (allocationCoordinate t a u) ^ 3 /
        (1 - (allocationCoordinate t a u) ^ 4) ^ 2)⁻¹ u := by
  have hx0 := allocationCoordinate_pos ht ha hu
  have hx1 := (allocationCoordinate_range ht ha hu.le).2
  apply HasDerivAt.of_local_left_inverse (continuousAt_allocationCoordinate ht ha hu)
    (hasDerivAt_allocationCost hx0.le hx1)
    (ne_of_gt (allocationCost_derivative_pos ht ha hx0 hx1))
  exact (eventually_gt_nhds hu).mono fun y hy => allocationCost_coordinate ht ha hy.le

/-- The positive marginal of the weighted summand in the original allocation
variables, written in the transformed coordinate. -/
noncomputable def allocationMarginal (t a u : ℝ) : ℝ :=
  (1 - (allocationCoordinate t a u) ^ 4) ^ 2 /
    (4 * t ^ 2 * a * (allocationCoordinate t a u) ^ 3)

theorem allocationMarginal_pos {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    0 < allocationMarginal t a u := by
  have hx0 := allocationCoordinate_pos ht ha hu
  have hx1 := (allocationCoordinate_range ht ha hu.le).2
  have hden : 0 < 1 - (allocationCoordinate t a u) ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  unfold allocationMarginal
  positivity

theorem hasDerivAt_allocationSummand {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => a * allocationCoordinate t a v)
      (allocationMarginal t a u) u := by
  have hx0 := allocationCoordinate_pos ht ha hu
  have hx1 := (allocationCoordinate_range ht ha hu.le).2
  have hden : 0 < 1 - (allocationCoordinate t a u) ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hx0.le hx1)
  apply ((hasDerivAt_allocationCoordinate ht ha hu).const_mul a).congr_deriv
  unfold allocationMarginal
  field_simp [ne_of_gt ht, ne_of_gt ha, ne_of_gt hx0, ne_of_gt hden]

/-- The marginal's defining rational identity, used after equality of marginals
has actually been derived from feasible variations. -/
theorem allocationMarginal_identity {t a u : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hu : 0 < u) :
    (4 * t ^ 2 * allocationMarginal t a u) *
        (a * (allocationCoordinate t a u) ^ 3) =
      (1 - (allocationCoordinate t a u) ^ 4) ^ 2 := by
  have hx0 := allocationCoordinate_pos ht ha hu
  unfold allocationMarginal
  field_simp [ne_of_gt ht, ne_of_gt ha, ne_of_gt hx0]

theorem allocation_sum_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (j : ι) (s : ℝ) :
    (∑ i, Function.update u j s i) = (∑ i, u i) + s - u j := by
  have h := allocation_sum_update_add u j (s - u j)
  have hid : u j + (s - u j) = s := by ring
  rw [hid] at h
  linarith only [h]

theorem allocationObjective_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (a u : ι → ℝ) (j : ι) (s : ℝ) :
    allocationObjective t a (Function.update u j s) =
      allocationObjective t a u + a j * allocationCoordinate t (a j) s -
        a j * allocationCoordinate t (a j) (u j) := by
  have hfun : (fun i => a i * allocationCoordinate t (a i) (Function.update u j s i)) =
      Function.update (fun i => a i * allocationCoordinate t (a i) (u i)) j
        (a j * allocationCoordinate t (a j) s) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hij]
  unfold allocationObjective
  rw [hfun, allocation_sum_update_eq]

/-- A concrete mass transfer between two coordinates. -/
noncomputable def allocationTransfer {ι : Type*} [DecidableEq ι]
    (u : ι → ℝ) (i j : ι) (s : ℝ) : ι → ℝ :=
  Function.update (Function.update u i (u i + s)) j (u j - s)

theorem allocationTransfer_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    (∑ k, allocationTransfer u i j s k) = ∑ k, u k := by
  simp only [allocationTransfer, allocation_sum_update_eq, Function.update_of_ne hij.symm]
  ring

theorem allocationTransfer_nonneg {ι : Type*} [DecidableEq ι]
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) {i j : ι} {s : ℝ}
    (hs : s ∈ Set.Ioo (-u i) (u j)) :
    ∀ k, 0 ≤ allocationTransfer u i j s k := by
  intro k
  dsimp only [allocationTransfer]
  by_cases hkj : k = j
  · subst k
    rw [Function.update_self]
    linarith only [hs.2]
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · subst k
      rw [Function.update_self]
      linarith only [hs.1]
    · rw [Function.update_of_ne hki]
      exact (hu k).le

theorem allocationTransfer_objective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) (a u : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    allocationObjective t a (allocationTransfer u i j s) =
      allocationObjective t a u +
        (a i * allocationCoordinate t (a i) (u i + s) +
          a j * allocationCoordinate t (a j) (u j - s)) -
        (a i * allocationCoordinate t (a i) (u i) +
          a j * allocationCoordinate t (a j) (u j)) := by
  simp only [allocationTransfer, allocationObjective_update_eq, Function.update_of_ne hij.symm]
  ring

/-- Equal marginal derivatives are derived from actual feasible pairwise
variations at an interior global optimizer. -/
theorem allocation_maximizer_marginals_eq {ι : Type*} [Fintype ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 < u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) (i j : ι) :
    allocationMarginal t (a i) (u i) = allocationMarginal t (a j) (u j) := by
  classical
  by_cases hij : i = j
  · subst i
    rfl
  let f : ℝ → ℝ := fun s =>
    a i * allocationCoordinate t (a i) (u i + s) +
      a j * allocationCoordinate t (a j) (u j - s)
  have hmem : (0 : ℝ) ∈ Set.Ioo (-u i) (u j) := by
    constructor
    · linarith only [hu0 i]
    · exact hu0 j
  have hlocal : IsLocalMax f 0 := by
    change ∀ᶠ s in 𝓝 (0 : ℝ), f s ≤ f 0
    apply Filter.Eventually.mono (isOpen_Ioo.mem_nhds hmem)
    intro s hs
    have hv0 := allocationTransfer_nonneg hu0 hs
    have hv1 : (∑ k, allocationTransfer u i j s k) ≤ 1 := by
      rw [allocationTransfer_sum u hij s]
      exact hu1
    have hm := hmax (allocationTransfer u i j s) hv0 hv1
    rw [allocationTransfer_objective t a u hij s] at hm
    dsimp only [f]
    simp only [add_zero, sub_zero]
    linarith only [hm]
  have hi : HasDerivAt
      (fun s : ℝ => a i * allocationCoordinate t (a i) (u i + s))
      (allocationMarginal t (a i) (u i)) 0 := by
    apply HasDerivAt.comp_const_add
      (f := fun v : ℝ => a i * allocationCoordinate t (a i) v) (u i) 0
    simpa only [add_zero] using hasDerivAt_allocationSummand ht (ha i) (hu0 i)
  have hj : HasDerivAt
      (fun s : ℝ => a j * allocationCoordinate t (a j) (u j - s))
      (-(allocationMarginal t (a j) (u j))) 0 := by
    apply HasDerivAt.comp_const_sub
      (f := fun v : ℝ => a j * allocationCoordinate t (a j) v) (u j) 0
    simpa only [sub_zero] using hasDerivAt_allocationSummand ht (ha j) (hu0 j)
  have hz := hlocal.hasDerivAt_eq_zero (hi.add hj)
  linarith only [hz]

/-- The first KKT equation is constructed from the actual common positive
marginal at an interior optimizer.  No stationarity equation is assumed. -/
theorem allocation_maximizer_kkt_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 < u i) (hu1 : (∑ i, u i) ≤ 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    ∃ β : ℝ, 0 < β ∧ ∀ i,
      a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
        β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2 := by
  classical
  let j : ι := Classical.choice (inferInstance : Nonempty ι)
  let lam : ℝ := allocationMarginal t (a j) (u j)
  have hlam : 0 < lam := allocationMarginal_pos ht (ha j) (hu0 j)
  have hfactor : 0 < 4 * t ^ 2 * lam := by positivity
  let β : ℝ := (4 * t ^ 2 * lam)⁻¹
  refine ⟨β, inv_pos.mpr hfactor, ?_⟩
  intro i
  have hmarg := allocation_maximizer_marginals_eq ht ha hu0 hu1 hmax i j
  have hidentity := allocationMarginal_identity ht (ha i) (hu0 i)
  rw [hmarg] at hidentity
  change (4 * t ^ 2 * lam) * (a i * (allocationCoordinate t (a i) (u i)) ^ 3) =
    (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2 at hidentity
  calc
    a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
        (4 * t ^ 2 * lam)⁻¹ *
          ((4 * t ^ 2 * lam) * (a i * (allocationCoordinate t (a i) (u i)) ^ 3)) := by
      field_simp [ne_of_gt hfactor]
    _ = β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2 := by
      rw [hidentity]

/-- Both KKT equations for an actual interior saturated optimizer.  The scalar
is constructed from feasible variations, then the second equation follows from
the already proved inverse-map budget identity. -/
theorem allocation_optimizer_kkt {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a u : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i)
    (hu0 : ∀ i, 0 < u i) (hu1 : (∑ i, u i) = 1)
    (hmax : ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
      allocationObjective t a v ≤ allocationObjective t a u) :
    ∃ β : ℝ, 0 < β ∧
      (∀ i, a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
        β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2) ∧
      1 = t ^ 2 * β * ∑ i,
        a i * allocationCoordinate t (a i) (u i) *
          (1 - (allocationCoordinate t (a i) (u i)) ^ 4) := by
  obtain ⟨β, hβ, hstationary⟩ := allocation_maximizer_kkt_exists ht ha hu0 hu1.le hmax
  refine ⟨β, hβ, hstationary, ?_⟩
  exact allocation_constructed_kkt_budget Finset.univ t β a u ht
    (fun i _ => ha i) (fun i _ => (hu0 i).le) (fun i _ => hstationary i) hu1

/-- The manuscript's original finite optimization problem has an actual
strictly positive full-budget optimizer and a positive scalar satisfying both
displayed KKT equations.  Existence, interiority, and stationarity are all
constructed from the positive masses and time. -/
theorem exists_manuscript_allocation_optimizer_kkt
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {t : ℝ} {a : ι → ℝ} (ht : 0 < t) (ha : ∀ i, 0 < a i) :
    ∃ (u : ι → ℝ) (β : ℝ), (∀ i, 0 < u i) ∧ (∑ i, u i) = 1 ∧
      (∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i) ≤ 1 →
        (∑ i, a i * (v i / (v i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ≤
          ∑ i, a i * (u i / (u i + t ^ 2 * (a i) ^ 2)) ^ (1 / (4 : ℝ))) ∧
      0 < β ∧
      (∀ i, a i * (allocationCoordinate t (a i) (u i)) ^ 3 =
        β * (1 - (allocationCoordinate t (a i) (u i)) ^ 4) ^ 2) ∧
      1 = t ^ 2 * β * ∑ i,
        a i * allocationCoordinate t (a i) (u i) *
          (1 - (allocationCoordinate t (a i) (u i)) ^ 4) := by
  obtain ⟨u, hu0, hu1, hmax⟩ := exists_positive_saturated_allocation_maximizer ht ha
  obtain ⟨β, hβ, hstationary, hbudget⟩ := allocation_optimizer_kkt ht ha hu0 hu1 hmax
  refine ⟨u, β, hu0, hu1, ?_, hβ, hstationary, hbudget⟩
  intro v hv0 hv1
  rw [← allocationObjective_eq_rpow ht ha hv0,
    ← allocationObjective_eq_rpow ht ha (fun i => (hu0 i).le)]
  exact hmax v hv0 hv1

end IdentityTesting
