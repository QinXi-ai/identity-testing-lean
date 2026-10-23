import IdentityTesting.CountableFiniteApproximation
import IdentityTesting.AllocationScaling
import IdentityTesting.AllocationMassLipschitz

/-! The manuscript's normalized truncation on the original alphabet.
The harmless zero-prefix fallback makes this a sequence of actual laws for all
indices; every formula below states the exact nonempty-prefix hypothesis. -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace IdentityTesting

private theorem normalized_discreteLaw_ext {p q : DiscreteLaw}
    (h : ∀ i, p.mass i = q.mass i) : p = q := by
  cases p
  cases q
  congr 1
  exact funext h

theorem prefix_retained_mass (q : DiscreteLaw) (m : ℕ) :
    (∑' i, truncatedMass q.mass (Finset.range m) i) =
      1 - residualMass q (Finset.range m) := by
  have h := q.summable.sum_add_tsum_compl (s := Finset.range m)
  rw [q.total] at h
  rw [tsum_eq_sum (s := Finset.range m) (fun i hi => by simp [truncatedMass, hi])]
  have he : (∑ i ∈ Finset.range m, truncatedMass q.mass (Finset.range m) i) =
      ∑ i ∈ Finset.range m, q.mass i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [truncatedMass, hi]
  rw [he]
  change (∑ i ∈ Finset.range m, q.mass i) + residualMass q (Finset.range m) = 1 at h
  linarith

def prefixNormalizedLaw (q : DiscreteLaw) (m : ℕ) : DiscreteLaw :=
  if h : residualMass q (Finset.range m) < 1 then
    { mass := fun i => (1 - residualMass q (Finset.range m))⁻¹ *
        truncatedMass q.mass (Finset.range m) i
      nonneg := fun i => mul_nonneg (inv_nonneg.mpr (by linarith))
        (truncatedMass_nonneg q.nonneg _ i)
      summable := (truncatedMass_summable q.mass _).mul_left _
      total := by
        rw [tsum_mul_left, prefix_retained_mass]
        exact inv_mul_cancel₀ (by linarith) }
  else prefixPooledLaw q 0

theorem prefixNormalizedLaw_mass (q : DiscreteLaw) (m i : ℕ)
    (hr : residualMass q (Finset.range m) < 1) :
    (prefixNormalizedLaw q m).mass i =
      if i < m then q.mass i / (1 - residualMass q (Finset.range m)) else 0 := by
  simp [prefixNormalizedLaw, hr, truncatedMass, Finset.mem_range, div_eq_mul_inv, mul_comm]

theorem prefixNormalizedLaw_mass_zero (q : DiscreteLaw) (m i : ℕ)
    (hi : m + 1 ≤ i) : (prefixNormalizedLaw q m).mass i = 0 := by
  by_cases hr : residualMass q (Finset.range m) < 1
  · rw [prefixNormalizedLaw_mass q m i hr, if_neg (by omega)]
  · simp only [prefixNormalizedLaw, dif_neg hr]
    exact prefixPooledLaw_mass_zero q 0 i (by omega)

def prefixNormalizedFinite (q : DiscreteLaw) (m : ℕ) :
    FiniteTesting.Probability (Fin (m + 1)) where
  mass i := (prefixNormalizedLaw q m).mass i.val
  nonneg i := (prefixNormalizedLaw q m).nonneg i.val
  total := by
    have hs : (∑' i, (prefixNormalizedLaw q m).mass i) =
        ∑ i ∈ Finset.range (m + 1), (prefixNormalizedLaw q m).mass i :=
      tsum_eq_sum (s := Finset.range (m + 1))
        (fun i hi => prefixNormalizedLaw_mass_zero q m i (Nat.le_of_not_gt (by
          simpa only [Finset.mem_range] using hi)))
    exact (Fin.sum_univ_eq_sum_range (prefixNormalizedLaw q m).mass (m + 1)).trans
      (hs.symm.trans (prefixNormalizedLaw q m).total)

theorem extendFiniteLaw_prefixNormalizedFinite (q : DiscreteLaw) (m : ℕ) :
    extendFiniteLaw (prefixNormalizedFinite q m) = prefixNormalizedLaw q m := by
  have he : ∀ i, (extendFiniteLaw (prefixNormalizedFinite q m)).mass i =
      (prefixNormalizedLaw q m).mass i := by
    intro i
    by_cases hi : i < m + 1
    · exact extendFiniteLaw_mass_val (prefixNormalizedFinite q m) ⟨i, hi⟩
    · rw [extendFiniteLaw_mass_of_not_lt _ i hi,
        prefixNormalizedLaw_mass_zero q m i (Nat.le_of_not_gt hi)]
  exact normalized_discreteLaw_ext he

/-- Exact TV error of the normalized truncation, on the original Nat labels. -/
theorem totalVariation_prefixNormalized (q : DiscreteLaw) (m : ℕ)
    (hr : residualMass q (Finset.range m) < 1) :
    totalVariation (prefixNormalizedLaw q m) q = residualMass q (Finset.range m) := by
  have hr0 : 0 ≤ residualMass q (Finset.range m) := tsum_nonneg (fun i => q.nonneg i)
  have hden : 0 < 1 - residualMass q (Finset.range m) := by linarith
  rw [totalVariation_eq_one_sub_overlap]
  have he : (fun i => min ((prefixNormalizedLaw q m).mass i) (q.mass i)) =
      truncatedMass q.mass (Finset.range m) := by
    funext i
    rw [prefixNormalizedLaw_mass q m i hr]
    by_cases hi : i < m
    · simp only [if_pos hi, truncatedMass, Finset.mem_range, hi, ↓reduceIte]
      apply min_eq_right
      apply (le_div_iff₀ hden).2
      nlinarith [mul_nonneg (q.nonneg i) hr0]
    · simp [hi, truncatedMass, q.nonneg i]
  rw [he, prefix_retained_mass]
  ring

theorem eventually_prefix_residual_lt_one (q : DiscreteLaw) :
    ∀ᶠ m in atTop, residualMass q (Finset.range m) < 1 :=
  (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds (by norm_num))

theorem prefixNormalized_l1_tendsto_zero (q : DiscreteLaw) :
    Tendsto (fun m => ∑' i, |(prefixNormalizedLaw q m).mass i - q.mass i|)
      atTop (𝓝 0) := by
  have he : (fun m => ∑' i, |(prefixNormalizedLaw q m).mass i - q.mass i|) =ᶠ[atTop]
      (fun m => 2 * residualMass q (Finset.range m)) := by
    filter_upwards [eventually_prefix_residual_lt_one q] with m hm
    have h := totalVariation_prefixNormalized q m hm
    unfold totalVariation at h
    linarith
  apply Tendsto.congr' he.symm
  simpa only [mul_zero] using (prefixResidual_tendsto_zero q).const_mul (2 : ℝ)

/-- Literal equation count:normalized-allocation, with the original allocationD. -/
theorem allocationD_prefixNormalized_scaling (q : DiscreteLaw) (m : ℕ)
    (hr : residualMass q (Finset.range m) < 1) (t : ℝ) :
    allocationD (prefixNormalizedLaw q m).mass t =
      (1 - residualMass q (Finset.range m))⁻¹ *
        allocationD (truncatedMass q.mass (Finset.range m))
          (t / (1 - residualMass q (Finset.range m))) := by
  simp only [prefixNormalizedLaw, dif_pos hr]
  rw [allocationD_mass_scale (truncatedMass_nonneg q.nonneg _)
    (truncatedMass_summable q.mass _) (inv_nonneg.mpr (by linarith))]
  rw [div_eq_mul_inv, mul_comm t]

/-- Uniform over every real time, hence over each compact positive-time interval. -/
theorem allocationD_prefixNormalized_abs_le (q : DiscreteLaw) (m : ℕ)
    (hr : residualMass q (Finset.range m) < 1) (t : ℝ) :
    |allocationD (prefixNormalizedLaw q m).mass t - allocationD q.mass t| ≤
      2 * residualMass q (Finset.range m) := by
  have h := allocationD_abs_sub_le_l1 t (prefixNormalizedLaw q m).nonneg q.nonneg
    (prefixNormalizedLaw q m).summable q.summable
  have htv := totalVariation_prefixNormalized q m hr
  unfold totalVariation at htv
  linarith

theorem allocationD_prefixNormalized_tendsto (q : DiscreteLaw) (t : ℝ) :
    Tendsto (fun m => allocationD (prefixNormalizedLaw q m).mass t) atTop
      (𝓝 (allocationD q.mass t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) _ (prefixNormalized_l1_tendsto_zero q)
  intro m
  exact allocationD_abs_sub_le_l1 t (prefixNormalizedLaw q m).nonneg q.nonneg
    (prefixNormalizedLaw q m).summable q.summable

end IdentityTesting
