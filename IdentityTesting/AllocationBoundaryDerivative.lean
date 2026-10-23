import IdentityTesting.AllocationExplicitDerivatives
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The infinite right derivative at the zero-allocation boundary. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

theorem allocation_summand_derivative_tendsto_zero_right {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (deriv (fun u : ℝ => a * (u / (u + c)) ^ (1 / 4 : ℝ)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hinv : Tendsto (fun u : ℝ => (u⁻¹) ^ (3 / 4 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_inv_nhdsGT_zero
  have hpow : Tendsto (fun u : ℝ => u ^ (-3 / 4 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    apply hinv.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Real.inv_rpow hu.le, show (-3 / 4 : ℝ) = -(3 / 4) by ring,
      Real.rpow_neg hu.le]
  have hcontinuous : ContinuousAt (fun u : ℝ => a * c / 4 * (u + c) ^ (-5 / 4 : ℝ)) 0 := by
    apply continuousAt_const.mul
    apply ContinuousAt.rpow_const (continuousAt_id.add continuousAt_const)
    left
    simpa using ne_of_gt hc
  have hcoeff : 0 < a * c / 4 * c ^ (-5 / 4 : ℝ) := by positivity
  have hlimit : Tendsto (fun u : ℝ => a * c / 4 * (u + c) ^ (-5 / 4 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * c / 4 * c ^ (-5 / 4 : ℝ))) := by
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  apply (hlimit.pos_mul_atTop hcoeff hpow).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [(hasDerivAt_allocation_summand_formula hc hu).deriv]
  ring

end IdentityTesting
