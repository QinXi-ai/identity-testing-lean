import IdentityTesting.CountableRoots
import IdentityTesting.HeavyRoots

/-! Actual roots for arbitrary nonnegative summable mass vectors.
No normalization, finite-support, or supplied regularity certificate is used. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IdentityTesting

def generalAllocationRoot (a : ℕ → ℝ) (e : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ allocationD a t ≤ e}

def generalHeavyAllocationFunction (a : ℕ → ℝ) (r t : ℝ) : ℝ :=
  allocationD a t + Real.sqrt (r / t)

def generalHeavyRoot (a : ℕ → ℝ) (r e : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ generalHeavyAllocationFunction a r t ≤ e}

theorem exists_positive_of_positive_tsum {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hr : 0 < ∑' i, a i) : ∃ i, 0 < a i := by
  by_contra h
  have hz : a = fun _ => 0 := by
    funext i
    exact le_antisymm (le_of_not_gt (fun hi => h ⟨i, hi⟩)) (ha i)
  simp only [hz, tsum_zero, lt_self_iff_false] at hr

/-- The root theorem of count:allocation for any positive total mass. -/
theorem exists_unique_generalAllocation_root {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he : 0 < e) (her : e < ∑' i, a i) :
    ∃! t : ℝ, 0 < t ∧ allocationD a t = e := by
  have hr := he.trans her
  exact exists_unique_positive_root
    (continuousOn_allocationD ha hs)
    (allocationD_strictAntiOn ha hs (exists_positive_of_positive_tsum ha hr))
    (allocationD_tendsto_mass_zero_right ha hs hr)
    (allocationD_tendsto_zero_atTop ha hs) he her

theorem generalAllocationRoot_spec {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he : 0 < e) (her : e < ∑' i, a i) :
    0 < generalAllocationRoot a e ∧ allocationD a (generalAllocationRoot a e) = e := by
  obtain ⟨t, ht, _⟩ := exists_unique_generalAllocation_root ha hs he her
  unfold generalAllocationRoot
  rw [positive_sublevel_sInf_eq
    (allocationD_strictAntiOn ha hs (exists_positive_of_positive_tsum ha (he.trans her)))
    ht.1 ht.2]
  exact ht

theorem generalAllocationRoot_unique {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e t : ℝ}
    (he : 0 < e) (her : e < ∑' i, a i) (ht : 0 < t) (hroot : allocationD a t = e) :
    t = generalAllocationRoot a e := by
  have hspec := generalAllocationRoot_spec ha hs he her
  exact (allocationD_strictAntiOn ha hs
    (exists_positive_of_positive_tsum ha (he.trans her))).injOn ht hspec.1
      (hroot.trans hspec.2.symm)

theorem continuousOn_generalHeavyAllocationFunction {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (r : ℝ) :
    ContinuousOn (generalHeavyAllocationFunction a r) (Ioi 0) := by
  apply (continuousOn_allocationD ha hs).add
  exact (continuousOn_const.div continuousOn_id (fun _ ht => ne_of_gt ht)).sqrt

theorem strictAntiOn_generalHeavyAllocationFunction {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (generalHeavyAllocationFunction a r) (Ioi 0) := by
  intro t ht s hs0 hts
  have hD := allocationD_antitone ha hs ht.le hts.le
  have hcount : Real.sqrt (r / s) < Real.sqrt (r / t) :=
    Real.sqrt_lt_sqrt (div_nonneg hr.le hs0.le) (div_lt_div_of_pos_left hr ht hts)
  exact add_lt_add_of_le_of_lt hD hcount

theorem generalHeavyAllocationFunction_tendsto_zero_atTop {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (r : ℝ) :
    Tendsto (generalHeavyAllocationFunction a r) atTop (𝓝 0) := by
  have hratio : Tendsto (fun t : ℝ => r / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun t : ℝ => r * t⁻¹) atTop (𝓝 (r * 0)))
  have hcount : Tendsto (fun t : ℝ => Real.sqrt (r / t)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hratio.sqrt
  simpa only [generalHeavyAllocationFunction, add_zero] using
    (allocationD_tendsto_zero_atTop ha hs).add hcount

theorem generalHeavyAllocationFunction_tendsto_atTop_zero {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r : ℝ} (hr : 0 < r) :
    Tendsto (generalHeavyAllocationFunction a r) (𝓝[>] (0 : ℝ)) atTop := by
  have hratio : Tendsto (fun t : ℝ => r / t) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using
      (Tendsto.const_mul_atTop hr tendsto_inv_nhdsGT_zero)
  have hcount : Tendsto (fun t : ℝ => Real.sqrt (r / t)) (𝓝[>] (0 : ℝ)) atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hratio.eventually_ge_atTop (b ^ 2)] with t ht
    exact Real.le_sqrt_of_sq_le ht
  apply tendsto_atTop_mono (fun t => ?_) hcount
  exact le_add_of_nonneg_left (allocationD_bounds t ha hs).1

/-- The count coefficient may be any positive r; in count:allocation it is Σa. -/
theorem exists_unique_generalHeavy_root {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e : ℝ} (hr : 0 < r) (he : 0 < e) :
    ∃! t : ℝ, 0 < t ∧ generalHeavyAllocationFunction a r t = e :=
  exists_unique_positive_root_of_top_limit
    (continuousOn_generalHeavyAllocationFunction ha hs r)
    (strictAntiOn_generalHeavyAllocationFunction ha hs hr)
    (generalHeavyAllocationFunction_tendsto_atTop_zero ha hs hr)
    (generalHeavyAllocationFunction_tendsto_zero_atTop ha hs r) he

theorem generalHeavyRoot_spec {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e : ℝ} (hr : 0 < r) (he : 0 < e) :
    0 < generalHeavyRoot a r e ∧
      allocationD a (generalHeavyRoot a r e) + Real.sqrt (r / generalHeavyRoot a r e) = e := by
  obtain ⟨t, ht, _⟩ := exists_unique_generalHeavy_root ha hs hr he
  have hid : generalHeavyRoot a r e = t :=
    positive_sublevel_sInf_eq (strictAntiOn_generalHeavyAllocationFunction ha hs hr) ht.1 ht.2
  rw [hid]
  exact ht

theorem generalHeavyRoot_unique {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e t : ℝ}
    (hr : 0 < r) (he : 0 < e) (ht : 0 < t)
    (hroot : allocationD a t + Real.sqrt (r / t) = e) : t = generalHeavyRoot a r e := by
  have hspec := generalHeavyRoot_spec ha hs hr he
  exact (strictAntiOn_generalHeavyAllocationFunction ha hs hr).injOn ht hspec.1
    (hroot.trans hspec.2.symm)

/-- Both original equations for a general vector of total mass r, explicitly
with actual infimum-defined roots and without analytic assumptions on D. -/
theorem summable_allocation_positive_roots {a : ℕ → ℝ} {r e f : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (htotal : ∑' i, a i = r)
    (hr : 0 < r) (he : 0 < e) (her : e < r) (hf : 0 < f) :
    (0 < generalAllocationRoot a e ∧ allocationD a (generalAllocationRoot a e) = e) ∧
      (0 < generalHeavyRoot a r f ∧ allocationD a (generalHeavyRoot a r f) +
        Real.sqrt (r / generalHeavyRoot a r f) = f) := by
  exact ⟨generalAllocationRoot_spec ha hs he (htotal ▸ her),
    generalHeavyRoot_spec ha hs hr hf⟩

theorem generalAllocationRoot_eq_allocationRoot (q : DiscreteLaw) (e : ℝ) :
    generalAllocationRoot q.mass e = allocationRoot q e := rfl

theorem generalHeavyRoot_eq_heavyRoot (q : DiscreteLaw) (e : ℝ) :
    generalHeavyRoot (tailMasses q) (1 - largestMass q) e = heavyRoot q e := rfl

end IdentityTesting
