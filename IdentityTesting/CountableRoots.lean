import IdentityTesting.CountableAllocationContinuity
import IdentityTesting.CountableAllocationStrict
import IdentityTesting.CountableAllocationLimits
import IdentityTesting.PositiveRoot
import IdentityTesting.LargestAtom

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IdentityTesting

/-- The all-atom equation from the manuscript has a unique positive solution
for every normalized countable reference, including references with zero atoms. -/
theorem exists_unique_allocation_root (q : DiscreteLaw) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    ∃! t : ℝ, 0 < t ∧ allocationD q.mass t = e := by
  apply exists_unique_positive_root
    (continuousOn_allocationD q.nonneg q.summable)
    (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive)
    (allocationD_tendsto_mass_zero_right q.nonneg q.summable (by rw [q.total]; norm_num))
    (allocationD_tendsto_zero_atTop q.nonneg q.summable) he0
  simpa only [q.total] using he1

/-- The infimum-based definition in Target equals the manuscript's actual root. -/
theorem allocationRoot_spec (q : DiscreteLaw) {e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) :
    0 < allocationRoot q e ∧ allocationD q.mass (allocationRoot q e) = e := by
  obtain ⟨t, ht, _⟩ := exists_unique_allocation_root q he0 he1
  unfold allocationRoot
  rw [positive_sublevel_sInf_eq
    (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive) ht.1 ht.2]
  exact ht

theorem allocationRoot_unique (q : DiscreteLaw) {e t : ℝ}
    (he0 : 0 < e) (he1 : e < 1) (ht : 0 < t) (hroot : allocationD q.mass t = e) :
    t = allocationRoot q e := by
  have hs := allocationRoot_spec q he0 he1
  exact (allocationD_strictAntiOn q.nonneg q.summable q.exists_positive).injOn
    ht hs.1 (hroot.trans hs.2.symm)

end IdentityTesting
