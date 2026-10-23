import IdentityTesting.CountableAllocation
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Endpoint limits of the actual countable allocation supremum

At infinity every feasible coordinate is at most one, giving a single
summably dominated envelope for the supremum.  At zero the explicit feasible
allocation `u_i = a_i / sum a` gives the full-mass lower limit.  The proofs use
the actual `allocationD`, not an abstract envelope or an assumed optimizer.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace IdentityTesting

theorem allocationFeasible_coordinate_le_one_for_limits {u : ℕ → ℝ}
    (hu : AllocationFeasible u) (i : ℕ) : u i ≤ 1 :=
  (hu.2.1.le_tsum i (fun j _ => hu.1 j)).trans hu.2.2

/-- The unit-allocation summand uniformly bounds every feasible scalar
allocation coordinate. -/
theorem allocation_term_le_unit_envelope {a t u : ℝ}
    (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) ≤
      a * (1 / (1 + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ) := by
  by_cases huz : u = 0
  · simpa only [huz, zero_div, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero]
      using (allocation_term_bounds (t := t) ha (by norm_num : (0 : ℝ) ≤ 1)).1
  have hu : 0 < u := lt_of_le_of_ne hu0 (Ne.symm huz)
  have hc : 0 ≤ t ^ 2 * a ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hd0 : 0 < u + t ^ 2 * a ^ 2 := add_pos_of_pos_of_nonneg hu hc
  have hd1 : 0 < 1 + t ^ 2 * a ^ 2 := by positivity
  have hratio : u / (u + t ^ 2 * a ^ 2) ≤ 1 / (1 + t ^ 2 * a ^ 2) := by
    apply (div_le_div_iff₀ hd0 hd1).2
    have h := mul_nonneg hc (sub_nonneg.mpr hu1)
    nlinarith only [h]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hu0 hd0.le) hratio (by norm_num)) ha

/-- The envelope is uniform over the entire actual feasible set, so it also
bounds the allocation supremum.  The all-ones vector is only an envelope;
it is not incorrectly asserted to be a feasible countable allocation. -/
theorem allocationD_le_unit_envelope {a : ℕ → ℝ} (t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    allocationD a t ≤ countableAllocationObjective a t (fun _ => 1) := by
  apply csSup_le (allocation_values_nonempty a t)
  rintro v ⟨u, hu, rfl⟩
  exact (countableAllocationObjective_summable t ha hasum hu.1).tsum_le_tsum
    (fun i => allocation_term_le_unit_envelope (ha i) (hu.1 i)
      (allocationFeasible_coordinate_le_one_for_limits hu i))
    (countableAllocationObjective_summable t ha hasum (fun _ => by norm_num))

theorem allocation_unit_envelope_term_tendsto {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun t : ℝ => a * (1 / (1 + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
  by_cases haz : a = 0
  · simpa only [haz, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hpow : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hprod : Tendsto (fun t : ℝ => t ^ 2 * a ^ 2) atTop atTop :=
    Tendsto.atTop_mul_const (pow_pos hap 2) hpow
  have hden : Tendsto (fun t : ℝ => 1 + t ^ 2 * a ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hprod
  have hroot := hden.inv_tendsto_atTop.rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hweighted : Tendsto
      (fun t : ℝ => a * ((1 + t ^ 2 * a ^ 2)⁻¹) ^ (1 / 4 : ℝ))
      atTop (𝓝 (a * (0 : ℝ) ^ (1 / 4 : ℝ))) :=
    tendsto_const_nhds.mul hroot
  simpa [one_div] using hweighted

/-- Dominated convergence applies to the uniform envelope, not merely to each
fixed feasible allocation. -/
theorem allocation_unit_envelope_tendsto_zero {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    Tendsto (fun t : ℝ => countableAllocationObjective a t (fun _ => 1))
      atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun t : ℝ => fun i : ℕ => a i * (1 / (1 + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ))
    (g := fun _ : ℕ => (0 : ℝ)) hasum
    (fun i => allocation_unit_envelope_term_tendsto (ha i)) (Eventually.of_forall (by
      intro t i
      have hb := allocation_term_bounds (t := t) (ha i) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [Real.norm_of_nonneg hb.1] using hb.2))
  simpa only [countableAllocationObjective, tsum_zero] using h

/-- The actual countable allocation supremum tends to zero at infinity. -/
theorem allocationD_tendsto_zero_atTop {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) :
    Tendsto (allocationD a) atTop (𝓝 0) :=
  squeeze_zero (fun t => (allocationD_bounds t ha hasum).1)
    (fun t => allocationD_le_unit_envelope t ha hasum)
    (allocation_unit_envelope_tendsto_zero ha hasum)

/-- At any fixed positive allocation the scalar weighted term tends to its
full mass as time tends to zero. -/
theorem allocation_term_tendsto_zero_time {a u : ℝ} (hu : 0 < u) :
    Tendsto (fun t : ℝ => a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ))
      (𝓝 0) (𝓝 a) := by
  have hden : u + (0 : ℝ) ^ 2 * a ^ 2 ≠ 0 := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero]
      using ne_of_gt hu
  have hratio : ContinuousAt (fun t : ℝ => u / (u + t ^ 2 * a ^ 2)) 0 :=
    continuousAt_const.div
      (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)) hden
  have hterm : ContinuousAt
      (fun t : ℝ => a * (u / (u + t ^ 2 * a ^ 2)) ^ (1 / 4 : ℝ)) 0 :=
    continuousAt_const.mul (hratio.rpow_const (Or.inr (by norm_num)))
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, add_zero,
    div_self (ne_of_gt hu), Real.one_rpow, mul_one] using hterm.tendsto

/-- The mass-proportional allocation is an actual feasible countable witness
when the total mass is positive. -/
theorem proportional_allocation_feasible {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (htotal : 0 < ∑' i, a i) :
    AllocationFeasible (fun i => a i / (∑' j, a j)) := by
  refine ⟨(fun i => div_nonneg (ha i) htotal.le), hasum.div_const _, ?_⟩
  simp only [tsum_div_const, div_self (ne_of_gt htotal), le_refl]

/-- The concrete mass-proportional objective approaches the full countable
mass by a summably dominated termwise limit. -/
theorem proportional_allocation_objective_tendsto_mass {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (htotal : 0 < ∑' i, a i) :
    Tendsto (fun t : ℝ =>
      countableAllocationObjective a t (fun i => a i / (∑' j, a j)))
      (𝓝 0) (𝓝 (∑' i, a i)) := by
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun t : ℝ => fun i : ℕ => a i *
      ((a i / (∑' j, a j)) /
        ((a i / (∑' j, a j)) + t ^ 2 * a i ^ 2)) ^ (1 / 4 : ℝ))
    (g := a) hasum (by
      intro i
      by_cases haz : a i = 0
      · simpa only [haz, zero_mul] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
      · have hap : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm haz)
        exact allocation_term_tendsto_zero_time (div_pos hap htotal))
    (Eventually.of_forall (by
      intro t i
      have hb := allocation_term_bounds (t := t) (ha i) (div_nonneg (ha i) htotal.le)
      simpa only [Real.norm_of_nonneg hb.1] using hb.2))
  simpa only [countableAllocationObjective] using h

/-- The actual countable allocation supremum approaches the full mass at zero.
The lower bound comes from an explicitly constructed feasible allocation. -/
theorem allocationD_tendsto_mass_zero {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (htotal : 0 < ∑' i, a i) :
    Tendsto (allocationD a) (𝓝 0) (𝓝 (∑' i, a i)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (proportional_allocation_objective_tendsto_mass ha hasum htotal) tendsto_const_nhds
  · exact fun t => countableAllocationObjective_le_allocationD t ha hasum
      (proportional_allocation_feasible ha hasum htotal)
  · exact fun t => (allocationD_bounds t ha hasum).2

/-- The right-hand endpoint limit stated in the manuscript. -/
theorem allocationD_tendsto_mass_zero_right {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : Summable a) (htotal : 0 < ∑' i, a i) :
    Tendsto (allocationD a) (𝓝[>] (0 : ℝ)) (𝓝 (∑' i, a i)) :=
  (allocationD_tendsto_mass_zero ha hasum htotal).mono_left nhdsWithin_le_nhds

end IdentityTesting
