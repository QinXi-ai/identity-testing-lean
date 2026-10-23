import IdentityTesting.OracleCoordinateFamily

/-! Exact logarithmic elasticities of the actual coordinate and budget functions. -/

noncomputable section
open Filter
open scoped Topology
namespace IdentityTesting.RationalComputation

theorem hasDerivAt_coordinate_parameter {a y : ℝ} (hy : 0 < y ∧ y < 1) :
    HasDerivAt (fun x : ℝ => a * x ^ 3 / (1 - x ^ 4) ^ 2)
      (a * y ^ 2 * (3 + 5 * y ^ 4) / (1 - y ^ 4) ^ 3) y := by
  have hd : 1 - y ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hy.1.le hy.2))
  convert (((hasDerivAt_id y).pow 3).const_mul a).div
    (((hasDerivAt_const y 1).sub ((hasDerivAt_id y).pow 4)).pow 2) (pow_ne_zero 2 hd) using 1 <;>
    norm_num [id_eq] <;> field_simp <;> ring

theorem realOracleCoordinate_hasDerivAt {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    let y := realOracleCoordinate a β
    HasDerivAt (realOracleCoordinate a)
      (a * y ^ 2 * (3 + 5 * y ^ 4) / (1 - y ^ 4) ^ 3)⁻¹ β := by
  have hy := realOracleCoordinate_spec ha hβ
  have hyp := hy.1.1
  have hd : 0 < 1 - realOracleCoordinate a β ^ 4 :=
    sub_pos.mpr (allocation_fourth_lt_one hy.1.1.le hy.1.2)
  apply HasDerivAt.of_local_left_inverse (realOracleCoordinate_continuousAt ha hβ)
    (hasDerivAt_coordinate_parameter hy.1) (ne_of_gt (by positivity))
  filter_upwards [Ioi_mem_nhds hβ] with γ hγ
  have h := realOracleCoordinate_spec ha hγ
  exact (div_eq_iff (pow_ne_zero 2 (ne_of_gt
    (sub_pos.mpr (allocation_fourth_lt_one h.1.1.le h.1.2))))).2 h.2

theorem hasDerivAt_allocationCost_coordinate {t a y : ℝ} (hy : 0 < y ∧ y < 1) :
    HasDerivAt (allocationCost t a)
      (4 * t ^ 2 * a ^ 2 * y ^ 3 / (1 - y ^ 4) ^ 2) y := by
  have hd : 1 - y ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hy.1.le hy.2))
  unfold allocationCost
  convert (((hasDerivAt_id y).pow 4).const_mul (t ^ 2 * a ^ 2)).div
    ((hasDerivAt_const y 1).sub ((hasDerivAt_id y).pow 4)) hd using 1 <;>
    norm_num [id_eq] <;> field_simp <;> ring

theorem realOracleCoordinate_elasticities {a β t : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (ht : 0 < t) :
    let y := realOracleCoordinate a β
    β * deriv (realOracleCoordinate a) β / y = (1 - y ^ 4) / (3 + 5 * y ^ 4) ∧
    β * deriv (fun γ => allocationCost t a (realOracleCoordinate a γ)) β /
        allocationCost t a y = 4 / (3 + 5 * y ^ 4) := by
  dsimp only
  let y := realOracleCoordinate a β
  have hy := realOracleCoordinate_spec ha hβ
  have hy0 : y ≠ 0 := ne_of_gt hy.1.1
  have hd : 1 - y ^ 4 ≠ 0 := ne_of_gt (sub_pos.mpr (allocation_fourth_lt_one hy.1.1.le hy.1.2))
  have hp : 3 + 5 * y ^ 4 ≠ 0 := ne_of_gt (by positivity)
  have hc := realOracleCoordinate_hasDerivAt ha hβ
  have hu := (hasDerivAt_allocationCost_coordinate (t := t) (a := a) hy.1).comp β hc
  simp only [Function.comp_def] at hu
  rw [hc.deriv, hu.deriv]
  change β * (a * y ^ 2 * (3 + 5 * y ^ 4) / (1 - y ^ 4) ^ 3)⁻¹ / y =
      (1 - y ^ 4) / (3 + 5 * y ^ 4) ∧
    β * ((4 * t ^ 2 * a ^ 2 * y ^ 3 / (1 - y ^ 4) ^ 2) *
      (a * y ^ 2 * (3 + 5 * y ^ 4) / (1 - y ^ 4) ^ 3)⁻¹) /
      allocationCost t a y = 4 / (3 + 5 * y ^ 4)
  have heq : β = a * y ^ 3 / (1 - y ^ 4) ^ 2 := (eq_div_iff (pow_ne_zero 2 hd)).2 hy.2.symm
  rw [heq]
  constructor <;> dsimp only [allocationCost] <;>
    field_simp [hy0, hd, hp, ne_of_gt ha, ne_of_gt ht] <;> ring

theorem realOracleCoordinate_elasticity_bounds {a β t : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (ht : 0 < t) :
    let y := realOracleCoordinate a β
    β * deriv (realOracleCoordinate a) β / y ∈ Set.Icc 0 (1 / 3) ∧
    β * deriv (fun γ => allocationCost t a (realOracleCoordinate a γ)) β /
        allocationCost t a y ∈ Set.Icc (1 / 2) (4 / 3) := by
  dsimp only
  rw [(realOracleCoordinate_elasticities ha hβ ht).1,
    (realOracleCoordinate_elasticities ha hβ ht).2]
  have hy := realOracleCoordinate_spec ha hβ
  have h4 := allocation_fourth_lt_one hy.1.1.le hy.1.2
  have hp : 0 < 3 + 5 * realOracleCoordinate a β ^ 4 := by positivity
  refine ⟨⟨div_nonneg (by linarith) hp.le, (div_le_iff₀ hp).2 ?_⟩,
    ⟨(le_div_iff₀ hp).2 ?_, (div_le_iff₀ hp).2 ?_⟩⟩ <;>
    nlinarith only [h4, pow_nonneg hy.1.1.le 4]

end IdentityTesting.RationalComputation
