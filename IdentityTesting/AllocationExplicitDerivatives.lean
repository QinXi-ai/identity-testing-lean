import IdentityTesting.AllocationStrictConcavity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The two explicit derivatives printed in the allocation lemma. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting

private theorem rpow_shift_one {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x ^ (p + 1) = x * x ^ p := by
  rw [Real.rpow_add hx, Real.rpow_one]
  ring

theorem hasDerivAt_allocation_summand_formula {a c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => a * (x / (x + c)) ^ (1 / 4 : ℝ))
      (a * c / 4 * u ^ (-3 / 4 : ℝ) * (u + c) ^ (-5 / 4 : ℝ)) u := by
  have hv : 0 < u + c := add_pos hu hc
  have h1 := (Real.hasDerivAt_rpow_const (x := u) (p := (1 / 4 : ℝ)) (Or.inl (ne_of_gt hu))).const_mul a
  have h2 := ((hasDerivAt_id u).add_const c).rpow_const
    (p := (-1 / 4 : ℝ)) (Or.inl (ne_of_gt hv))
  have hf := h1.mul h2
  have hu1 : u ^ (1 / 4 : ℝ) = u * u ^ (-3 / 4 : ℝ) := by
    convert rpow_shift_one hu (-3 / 4) using 1 <;> norm_num
  have hv1 : (u + c) ^ (-1 / 4 : ℝ) = (u + c) * (u + c) ^ (-5 / 4 : ℝ) := by
    convert rpow_shift_one hv (-5 / 4) using 1 <;> norm_num
  have hd : HasDerivAt (fun x : ℝ => a * x ^ (1 / 4 : ℝ) * (x + c) ^ (-1 / 4 : ℝ))
      (a * c / 4 * u ^ (-3 / 4 : ℝ) * (u + c) ^ (-5 / 4 : ℝ)) u := by
    apply hf.congr_deriv
    norm_num only [id_eq] at *
    rw [hu1, hv1]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with x hx
  rw [Real.div_rpow hx.le (add_pos hx hc).le]
  norm_num only
  rw [Real.rpow_neg (add_nonneg hx.le hc.le)]
  ring

theorem hasDerivAt_allocation_first_derivative_formula {a c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => a * c / 4 * x ^ (-3 / 4 : ℝ) * (x + c) ^ (-5 / 4 : ℝ))
      (-a * c * (8 * u + 3 * c) / 16 * u ^ (-7 / 4 : ℝ) *
        (u + c) ^ (-9 / 4 : ℝ)) u := by
  have hv : 0 < u + c := add_pos hu hc
  have h1 := (Real.hasDerivAt_rpow_const (x := u) (p := (-3 / 4 : ℝ))
    (Or.inl (ne_of_gt hu))).const_mul (a * c / 4)
  have h2 := ((hasDerivAt_id u).add_const c).rpow_const
    (p := (-5 / 4 : ℝ)) (Or.inl (ne_of_gt hv))
  have hu1 : u ^ (-3 / 4 : ℝ) = u * u ^ (-7 / 4 : ℝ) := by
    convert rpow_shift_one hu (-7 / 4) using 1 <;> norm_num
  have hv1 : (u + c) ^ (-5 / 4 : ℝ) = (u + c) * (u + c) ^ (-9 / 4 : ℝ) := by
    convert rpow_shift_one hv (-9 / 4) using 1 <;> norm_num
  apply (h1.mul h2).congr_deriv
  norm_num only [id_eq] at *
  rw [hu1, hv1]
  ring

theorem allocation_summand_explicit_derivatives {a c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    deriv (fun x : ℝ => a * (x / (x + c)) ^ (1 / 4 : ℝ)) u =
        a * c / 4 * u ^ (-3 / 4 : ℝ) * (u + c) ^ (-5 / 4 : ℝ) ∧
      deriv (deriv (fun x : ℝ => a * (x / (x + c)) ^ (1 / 4 : ℝ))) u =
        -a * c * (8 * u + 3 * c) / 16 * u ^ (-7 / 4 : ℝ) * (u + c) ^ (-9 / 4 : ℝ) := by
  refine ⟨(hasDerivAt_allocation_summand_formula hc hu).deriv, ?_⟩
  apply HasDerivAt.deriv
  apply (hasDerivAt_allocation_first_derivative_formula (a := a) hc hu).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with x hx
  exact (hasDerivAt_allocation_summand_formula hc hx).deriv

end IdentityTesting
