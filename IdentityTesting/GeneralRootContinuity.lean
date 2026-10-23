import IdentityTesting.GeneralAllocationRoots
import IdentityTesting.CountableRootApproximation
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! The general root part of count:continuity.
Pointwise convergence suffices; the final wrappers accept the manuscript's
uniform convergence on all compact positive-time sets. Actual allocation
approximants supply their own monotonicity and eventual root existence. -/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IdentityTesting

/-- This also handles finitely many nonpositive count coefficients in a
convergent sequence, using the existing totalized real square-root definition. -/
theorem antitoneOn_sqrt_div (r : ℝ) :
    AntitoneOn (fun t : ℝ => Real.sqrt (r / t)) (Ioi 0) := by
  intro t ht s hs hts
  dsimp only
  by_cases hr : 0 ≤ r
  · exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hr ht hts)
  · have hr0 : r ≤ 0 := (lt_of_not_ge hr).le
    rw [Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr0 hs.le),
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr0 ht.le)]

/-- The count terms converge uniformly on every time set bounded away from
zero, as used in the manuscript's root-bracketing proof. -/
theorem sqrt_countTerm_tendstoUniformlyOn_Ici {rm : ℕ → ℝ} {r l : ℝ}
    (hl : 0 < l) (hrm : Tendsto rm atTop (𝓝 r)) :
    TendstoUniformlyOn (fun m t => Real.sqrt (rm m / t))
      (fun t => Real.sqrt (r / t)) atTop (Ici l) := by
  have hdiff : Tendsto (fun m => |Real.sqrt r - Real.sqrt (rm m)| / Real.sqrt l)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => Real.sqrt r) atTop (𝓝 (Real.sqrt r)) :=
      tendsto_const_nhds
    simpa only [sub_self, abs_zero, zero_div] using
      ((hc.sub hrm.sqrt).abs.div_const (Real.sqrt l))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hdiff.eventually (gt_mem_nhds hε)] with m hm t ht
  have ht0 : 0 ≤ t := hl.le.trans ht
  rw [Real.dist_eq, Real.sqrt_div' r ht0, Real.sqrt_div' (rm m) ht0,
    ← sub_div, abs_div, abs_of_nonneg (Real.sqrt_nonneg t)]
  exact (div_le_div_of_nonneg_left (abs_nonneg _)
    (Real.sqrt_pos.mpr hl) (Real.sqrt_le_sqrt ht)).trans_lt hm

theorem sqrt_countTerm_tendstoUniformlyOn_Icc {rm : ℕ → ℝ} {r l u : ℝ}
    (hl : 0 < l) (hrm : Tendsto rm atTop (𝓝 r)) :
    TendstoUniformlyOn (fun m t => Real.sqrt (rm m / t))
      (fun t => Real.sqrt (r / t)) atTop (Icc l u) :=
  (sqrt_countTerm_tendstoUniformlyOn_Ici hl hrm).mono (fun _ ht => ht.1)

/-- Arbitrary antitone approximants, with the limiting function instantiated
by the actual D of a nonnegative summable vector. -/
theorem tendsto_generalAllocation_roots {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he0 : 0 < e) (her : e < ∑' i, a i)
    {fm : ℕ → ℝ → ℝ} {em xm : ℕ → ℝ}
    (hm : ∀ m, AntitoneOn (fm m) (Ioi 0))
    (hconv : ∀ t, 0 < t → Tendsto (fun m => fm m t) atTop (𝓝 (allocationD a t)))
    (he : Tendsto em atTop (𝓝 e))
    (hroots : ∀ᶠ m in atTop, 0 < xm m ∧ fm m (xm m) = em m) :
    Tendsto xm atTop (𝓝 (generalAllocationRoot a e)) := by
  have hspec := generalAllocationRoot_spec ha hs he0 her
  exact tendsto_positive_roots hspec.1 hspec.2
    (allocationD_strictAntiOn ha hs (exists_positive_of_positive_tsum ha (he0.trans her)))
    hm hconv he hroots

/-- Arbitrary allocation-like approximants and changing count coefficients.
The count-term convergence is derived from rm → r at each bracket point. -/
theorem tendsto_generalHeavy_roots {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e : ℝ}
    (hr : 0 < r) (he0 : 0 < e)
    {fm : ℕ → ℝ → ℝ} {rm em xm : ℕ → ℝ}
    (hm : ∀ m, AntitoneOn (fm m) (Ioi 0))
    (hconv : ∀ t, 0 < t → Tendsto (fun m => fm m t) atTop (𝓝 (allocationD a t)))
    (hrm : Tendsto rm atTop (𝓝 r)) (he : Tendsto em atTop (𝓝 e))
    (hroots : ∀ᶠ m in atTop,
      0 < xm m ∧ fm m (xm m) + Real.sqrt (rm m / xm m) = em m) :
    Tendsto xm atTop (𝓝 (generalHeavyRoot a r e)) := by
  have hspec := generalHeavyRoot_spec ha hs hr he0
  apply tendsto_positive_roots (fm := fun m t => fm m t + Real.sqrt (rm m / t))
    (f := generalHeavyAllocationFunction a r) hspec.1 hspec.2
    (strictAntiOn_generalHeavyAllocationFunction ha hs hr) _ _ he hroots
  · intro m t ht s hs0 hts
    exact add_le_add (hm m ht hs0 hts) (antitoneOn_sqrt_div (rm m) ht hs0 hts)
  · intro t ht
    exact (hconv t ht).add (hrm.div_const t).sqrt

/-- For actual approximating mass vectors, convergence already ensures that
the targets eventually lie strictly between zero and the approximating mass. -/
theorem eventually_generalAllocationRoot_spec {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he0 : 0 < e) (her : e < ∑' i, a i)
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {em : ℕ → ℝ}
    (hconv : ∀ t, 0 < t → Tendsto (fun m => allocationD (am m) t) atTop
      (𝓝 (allocationD a t))) (he : Tendsto em atTop (𝓝 e)) :
    ∀ᶠ m in atTop, 0 < generalAllocationRoot (am m) (em m) ∧
      allocationD (am m) (generalAllocationRoot (am m) (em m)) = em m := by
  let T := generalAllocationRoot a e
  have hT := generalAllocationRoot_spec ha hs he0 her
  have hhalf : 0 < T / 2 := half_pos hT.1
  have hhalfT : T / 2 < T := half_lt_self hT.1
  have hgap : 0 < allocationD a (T / 2) - e := by
    have hstrict := allocationD_strict_antitone ha hs
      (exists_positive_of_positive_tsum ha (he0.trans her)) hhalf hhalfT
    rw [hT.2] at hstrict
    exact sub_pos.mpr hstrict
  have hnear : ∀ᶠ m in atTop, 0 < allocationD (am m) (T / 2) - em m :=
    ((hconv (T / 2) hhalf).sub he).eventually (Ioi_mem_nhds hgap)
  have hem : ∀ᶠ m in atTop, 0 < em m := he.eventually (Ioi_mem_nhds he0)
  filter_upwards [hnear, hem] with m hm hme
  apply generalAllocationRoot_spec (ham m) (hams m) hme
  exact (sub_pos.mp hm).trans_le (allocationD_bounds (T / 2) (ham m) (hams m)).2

theorem generalAllocationRoot_tendsto_of_pointwise {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he0 : 0 < e) (her : e < ∑' i, a i)
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {em : ℕ → ℝ}
    (hconv : ∀ t, 0 < t → Tendsto (fun m => allocationD (am m) t) atTop
      (𝓝 (allocationD a t))) (he : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => generalAllocationRoot (am m) (em m)) atTop
      (𝓝 (generalAllocationRoot a e)) := by
  apply tendsto_generalAllocation_roots ha hs he0 her _ hconv he
    (eventually_generalAllocationRoot_spec ha hs he0 her am ham hams hconv he)
  intro m t ht s hs0 hts
  exact allocationD_antitone (ham m) (hams m) ht.le hts

theorem eventually_generalHeavyRoot_spec
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {rm em : ℕ → ℝ} {r e : ℝ} (hr : 0 < r) (he0 : 0 < e)
    (hrm : Tendsto rm atTop (𝓝 r)) (he : Tendsto em atTop (𝓝 e)) :
    ∀ᶠ m in atTop, 0 < generalHeavyRoot (am m) (rm m) (em m) ∧
      allocationD (am m) (generalHeavyRoot (am m) (rm m) (em m)) +
        Real.sqrt (rm m / generalHeavyRoot (am m) (rm m) (em m)) = em m := by
  filter_upwards [hrm.eventually (Ioi_mem_nhds hr), he.eventually (Ioi_mem_nhds he0)]
    with m hmr hme
  exact generalHeavyRoot_spec (ham m) (hams m) hmr hme

theorem generalHeavyRoot_tendsto_of_pointwise {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e : ℝ}
    (hr : 0 < r) (he0 : 0 < e)
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {rm em : ℕ → ℝ}
    (hconv : ∀ t, 0 < t → Tendsto (fun m => allocationD (am m) t) atTop
      (𝓝 (allocationD a t)))
    (hrm : Tendsto rm atTop (𝓝 r)) (he : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => generalHeavyRoot (am m) (rm m) (em m)) atTop
      (𝓝 (generalHeavyRoot a r e)) := by
  apply tendsto_generalHeavy_roots ha hs hr he0 _ hconv hrm he
    (eventually_generalHeavyRoot_spec am ham hams hr he0 hrm he)
  intro m t ht s hs0 hts
  exact allocationD_antitone (ham m) (hams m) ht.le hts

/-- Uniform convergence on compact subsets implies the pointwise input used
by the root theorem; only singleton compact sets are needed. -/
theorem allocation_pointwise_of_uniform_on_compacts
    {fm : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hconv : ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K →
      TendstoUniformlyOn fm f atTop K) :
    ∀ t, 0 < t → Tendsto (fun m => fm m t) atTop (𝓝 (f t)) := by
  intro t ht
  apply (hconv {t} _ isCompact_singleton).tendsto_at (mem_singleton t)
  simpa only [singleton_subset_iff, mem_Ioi] using ht

/-- Original ordinary-root statement, for actual arbitrary approximating
allocation functions. Finite-support approximants are included. -/
theorem generalAllocationRoot_tendsto_on_compacts {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {e : ℝ}
    (he0 : 0 < e) (her : e < ∑' i, a i)
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {em : ℕ → ℝ}
    (hconv : ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K →
      TendstoUniformlyOn (fun m => allocationD (am m)) (allocationD a) atTop K)
    (he : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => generalAllocationRoot (am m) (em m)) atTop
      (𝓝 (generalAllocationRoot a e)) :=
  generalAllocationRoot_tendsto_of_pointwise ha hs he0 her am ham hams
    (allocation_pointwise_of_uniform_on_compacts hconv) he

/-- Original changing-count root statement, with the actual count term and
without requiring either rm or em to be positive for every initial index. -/
theorem generalHeavyRoot_tendsto_on_compacts {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) {r e : ℝ}
    (hr : 0 < r) (he0 : 0 < e)
    (am : ℕ → ℕ → ℝ) (ham : ∀ m i, 0 ≤ am m i) (hams : ∀ m, Summable (am m))
    {rm em : ℕ → ℝ}
    (hconv : ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K →
      TendstoUniformlyOn (fun m => allocationD (am m)) (allocationD a) atTop K)
    (hrm : Tendsto rm atTop (𝓝 r)) (he : Tendsto em atTop (𝓝 e)) :
    Tendsto (fun m => generalHeavyRoot (am m) (rm m) (em m)) atTop
      (𝓝 (generalHeavyRoot a r e)) :=
  generalHeavyRoot_tendsto_of_pointwise ha hs hr he0 am ham hams
    (allocation_pointwise_of_uniform_on_compacts hconv) hrm he

end IdentityTesting
