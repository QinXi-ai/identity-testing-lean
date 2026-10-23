import IdentityTesting.CountableAllocationContinuity
import IdentityTesting.CountableAllocationLimits
import IdentityTesting.LargestAtom
import IdentityTesting.PositiveRoot
import Mathlib.Data.Real.Sqrt

/-!
# The original heavy-root definition is an actual unique positive root

For `largestMass q < 1`, the square-root term is strictly decreasing and
diverges at zero from the right.  The countable allocation term is continuous,
nonnegative, antitone, and tends to zero at infinity.  These facts establish
the range and uniqueness of the combined function, and identify its positive
root with the exact sublevel infimum used by `heavyRoot` in `Target`.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace IdentityTesting

def heavyAllocationFunction (q : DiscreteLaw) (t : ℝ) : ℝ :=
  allocationD (tailMasses q) t + Real.sqrt ((1 - largestMass q) / t)

theorem continuousOn_heavyAllocationFunction (q : DiscreteLaw) :
    ContinuousOn (heavyAllocationFunction q) (Ioi 0) := by
  apply (continuousOn_allocationD (tailMasses_nonneg q) (tailMasses_summable q)).add
  exact (continuousOn_const.div continuousOn_id (fun _ ht => ne_of_gt ht)).sqrt

theorem strictAntiOn_heavyAllocationFunction (q : DiscreteLaw)
    (hq : largestMass q < 1) : StrictAntiOn (heavyAllocationFunction q) (Ioi 0) := by
  intro t ht r hr htr
  have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
  have hD := allocationD_antitone (tailMasses_nonneg q) (tailMasses_summable q)
    (le_of_lt ht) (le_of_lt htr)
  have hsqrt : Real.sqrt ((1 - largestMass q) / r) <
      Real.sqrt ((1 - largestMass q) / t) :=
    Real.sqrt_lt_sqrt (div_nonneg hR.le hr.le)
      (div_lt_div_of_pos_left hR ht htr)
  exact add_lt_add_of_le_of_lt hD hsqrt

theorem heavyAllocationFunction_tendsto_zero_atTop (q : DiscreteLaw) :
    Tendsto (heavyAllocationFunction q) atTop (𝓝 0) := by
  have hratio : Tendsto (fun t : ℝ => (1 - largestMass q) / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun t : ℝ => (1 - largestMass q) * t⁻¹) atTop
          (𝓝 ((1 - largestMass q) * 0)))
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt ((1 - largestMass q) / t))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hratio.sqrt
  simpa only [heavyAllocationFunction, add_zero] using
    (allocationD_tendsto_zero_atTop (tailMasses_nonneg q) (tailMasses_summable q)).add hsqrt

theorem heavyAllocationFunction_tendsto_atTop_zero (q : DiscreteLaw)
    (hq : largestMass q < 1) :
    Tendsto (heavyAllocationFunction q) (𝓝[>] (0 : ℝ)) atTop := by
  have hR : 0 < 1 - largestMass q := sub_pos.mpr hq
  have hratio : Tendsto (fun t : ℝ => (1 - largestMass q) / t)
      (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using
      (Tendsto.const_mul_atTop hR tendsto_inv_nhdsGT_zero)
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt ((1 - largestMass q) / t))
      (𝓝[>] (0 : ℝ)) atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hratio.eventually_ge_atTop (b ^ 2)] with t ht
    exact Real.le_sqrt_of_sq_le ht
  apply tendsto_atTop_mono (fun t => ?_) hsqrt
  exact le_add_of_nonneg_left
    (allocationD_bounds t (tailMasses_nonneg q) (tailMasses_summable q)).1

/-- The original sublevel infimum is positive and satisfies the heavy equation
for every positive target, not only targets bounded by the tail mass. -/
theorem heavyRoot_spec (q : DiscreteLaw) (hq : largestMass q < 1)
    {e : ℝ} (he : 0 < e) :
    0 < heavyRoot q e ∧ heavyAllocationFunction q (heavyRoot q e) = e := by
  have hm := strictAntiOn_heavyAllocationFunction q hq
  obtain ⟨t, ht, _⟩ := exists_unique_positive_root_of_top_limit
    (continuousOn_heavyAllocationFunction q) hm
    (heavyAllocationFunction_tendsto_atTop_zero q hq)
    (heavyAllocationFunction_tendsto_zero_atTop q) he
  have hroot : heavyRoot q e = t := by
    change sInf {r : ℝ | 0 < r ∧ heavyAllocationFunction q r ≤ e} = t
    exact positive_sublevel_sInf_eq hm ht.1 ht.2
  rw [hroot]
  exact ht

theorem heavyRoot_pos (q : DiscreteLaw) (hq : largestMass q < 1)
    {e : ℝ} (he : 0 < e) : 0 < heavyRoot q e :=
  (heavyRoot_spec q hq he).1

theorem heavyRoot_equation (q : DiscreteLaw) (hq : largestMass q < 1)
    {e : ℝ} (he : 0 < e) :
    allocationD (tailMasses q) (heavyRoot q e) +
      Real.sqrt ((1 - largestMass q) / heavyRoot q e) = e :=
  (heavyRoot_spec q hq he).2

theorem heavyRoot_unique (q : DiscreteLaw) (hq : largestMass q < 1)
    {e t : ℝ} (he : 0 < e) (ht : 0 < t)
    (hvalue : allocationD (tailMasses q) t + Real.sqrt ((1 - largestMass q) / t) = e) :
    t = heavyRoot q e := by
  have hroot := heavyRoot_spec q hq he
  exact (strictAntiOn_heavyAllocationFunction q hq).injOn ht hroot.1
    (hvalue.trans hroot.2.symm)

end IdentityTesting
