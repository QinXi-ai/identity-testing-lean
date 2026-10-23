import IdentityTesting.CountableFiniteApproximation
import IdentityTesting.HeavyRoots

/-! Largest-atom and heavy-function approximation for the actual finite pooled
references. The original selected largest label is eventually unchanged. -/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IdentityTesting

theorem prefixPooledLaw_mass_le_largest (q : DiscreteLaw) (m : ℕ)
    (hr : residualMass q (Finset.range m) ≤ largestMass q) (i : ℕ) :
    (prefixPooledLaw q m).mass i ≤ largestMass q := by
  by_cases hi : i < m
  · rw [prefixPooledLaw_mass_of_lt q m i hi, largestMass_eq_selected]
    exact largestIndex_spec q i
  · by_cases him : i = m
    · subst i
      rw [prefixPooledLaw_mass_residual]
      exact hr
    · rw [prefixPooledLaw_mass_zero q m i (by omega)]
      exact (largestMass_pos q).le

theorem largestMass_prefixPooled_eq (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) ≤ largestMass q) :
    largestMass (prefixPooledLaw q m) = largestMass q := by
  apply le_antisymm
  · rw [largestMass_eq_selected]
    exact prefixPooledLaw_mass_le_largest q m hr _
  · calc
      largestMass q = q.mass (largestIndex q) := largestMass_eq_selected q
      _ = (prefixPooledLaw q m).mass (largestIndex q) :=
        (prefixPooledLaw_mass_of_lt q m _ hm).symm
      _ ≤ (prefixPooledLaw q m).mass (largestIndex (prefixPooledLaw q m)) :=
        largestIndex_spec (prefixPooledLaw q m) _
      _ = _ := (largestMass_eq_selected _).symm

theorem largestIndex_prefixPooled_eq (q : DiscreteLaw) (m : ℕ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) ≤ largestMass q) :
    largestIndex (prefixPooledLaw q m) = largestIndex q := by
  have hmass := largestMass_prefixPooled_eq q m hm hr
  have hmax : ∀ i, (prefixPooledLaw q m).mass i ≤
      (prefixPooledLaw q m).mass (largestIndex q) := by
    intro i
    rw [prefixPooledLaw_mass_of_lt q m _ hm, ← largestMass_eq_selected]
    exact prefixPooledLaw_mass_le_largest q m hr i
  have hle : largestIndex (prefixPooledLaw q m) ≤ largestIndex q := Nat.sInf_le hmax
  have hlt : largestIndex (prefixPooledLaw q m) < m := hle.trans_lt hm
  have hmax' : ∀ i, q.mass i ≤ q.mass (largestIndex (prefixPooledLaw q m)) := by
    intro i
    calc
      q.mass i ≤ largestMass q := by rw [largestMass_eq_selected]; exact largestIndex_spec q i
      _ = largestMass (prefixPooledLaw q m) := hmass.symm
      _ = (prefixPooledLaw q m).mass (largestIndex (prefixPooledLaw q m)) :=
        largestMass_eq_selected _
      _ = _ := prefixPooledLaw_mass_of_lt q m _ hlt
  exact Nat.le_antisymm hle (Nat.sInf_le hmax')

theorem eventually_prefixPooled_head (q : DiscreteLaw) :
    ∀ᶠ m in atTop, largestIndex q < m ∧
      residualMass q (Finset.range m) ≤ largestMass q ∧
      largestMass (prefixPooledLaw q m) = largestMass q ∧
      largestIndex (prefixPooledLaw q m) = largestIndex q := by
  have hr : ∀ᶠ m in atTop, residualMass q (Finset.range m) < largestMass q :=
    (prefixResidual_tendsto_zero q).eventually (gt_mem_nhds (largestMass_pos q))
  filter_upwards [eventually_gt_atTop (largestIndex q), hr] with m hm hr
  exact ⟨hm, hr.le, largestMass_prefixPooled_eq q m hm hr.le,
    largestIndex_prefixPooled_eq q m hm hr.le⟩

theorem discardedMass_tailMasses_eq (q : DiscreteLaw) (m : ℕ) (hm : largestIndex q < m) :
    discardedMass (tailMasses q) (Finset.range m) = discardedMass q.mass (Finset.range m) := by
  apply tsum_congr
  intro i
  have hne : i.val ≠ largestIndex q := by
    intro hi
    have hlt : i.val < m := by rw [hi]; exact hm
    exact i.property (Finset.mem_range.mpr hlt)
  simp only [tailMasses, if_neg hne]

theorem allocationD_tail_prefixPooled_abs_le (q : DiscreteLaw) (m : ℕ) (t : ℝ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) ≤ largestMass q) :
    |allocationD (tailMasses (prefixPooledLaw q m)) t - allocationD (tailMasses q) t| ≤
      residualMass q (Finset.range m) := by
  have hindex := largestIndex_prefixPooled_eq q m hm hr
  have hlt : largestIndex (prefixPooledLaw q m) < m := by simpa only [hindex] using hm
  apply allocationD_abs_sub_le_tail (Finset.range m) t
    (tailMasses_nonneg _) (tailMasses_summable _)
    (tailMasses_nonneg q) (tailMasses_summable q)
  · intro i hi
    simp only [tailMasses, hindex]
    split_ifs
    · rfl
    · exact prefixPooledLaw_mass_of_lt q m i (Finset.mem_range.mp hi)
  · rw [discardedMass_tailMasses_eq _ m hlt, prefixPooledLaw_discardedMass]
  · rw [discardedMass_tailMasses_eq q m hm]
    exact le_rfl

theorem heavyAllocationFunction_prefixPooled_abs_le (q : DiscreteLaw) (m : ℕ) (t : ℝ)
    (hm : largestIndex q < m) (hr : residualMass q (Finset.range m) ≤ largestMass q) :
    |heavyAllocationFunction (prefixPooledLaw q m) t - heavyAllocationFunction q t| ≤
      residualMass q (Finset.range m) := by
  have h := allocationD_tail_prefixPooled_abs_le q m t hm hr
  simp only [heavyAllocationFunction, largestMass_prefixPooled_eq q m hm hr]
  simpa only [add_sub_add_right_eq_sub] using h

theorem heavyAllocationFunction_prefixPooled_tendsto (q : DiscreteLaw) (t : ℝ) :
    Tendsto (fun m => heavyAllocationFunction (prefixPooledLaw q m) t) atTop
      (𝓝 (heavyAllocationFunction q t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ (prefixResidual_tendsto_zero q)
  filter_upwards [eventually_prefixPooled_head q] with m hm
  simpa only [Real.norm_eq_abs] using heavyAllocationFunction_prefixPooled_abs_le q m t hm.1 hm.2.1

theorem heavyAllocationFunction_antitone (q : DiscreteLaw) :
    AntitoneOn (heavyAllocationFunction q) (Ioi 0) := by
  intro t ht r hr htr
  unfold heavyAllocationFunction
  apply add_le_add
  · exact allocationD_antitone (tailMasses_nonneg q) (tailMasses_summable q) ht.le htr
  · apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr (largestMass_le_one q)) ht htr

end IdentityTesting
