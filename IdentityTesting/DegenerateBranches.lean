import IdentityTesting.LargestAtom
import IdentityTesting.PointMassTesting

/-! Two complete branches of the original characterization, using its actual
`roundedScale` and countable randomized-test semantics. -/
noncomputable section
open scoped BigOperators
namespace IdentityTesting

theorem DiscreteLaw.eq_of_mass_eq {p q : DiscreteLaw} (h : p.mass = q.mass) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem DiscreteLaw.eq_pointMass_of_mass_one (q : DiscreteLaw) (j : ℕ)
    (hj : q.mass j = 1) : q = pointMass j := by
  apply DiscreteLaw.eq_of_mass_eq
  funext i
  by_cases hij : i = j
  · subst i
    simpa [pointMass] using hj
  · have hsum := q.summable.sum_le_tsum ({i, j} : Finset ℕ) (fun k _ => q.nonneg k)
    rw [Finset.sum_pair hij, hj, q.total] at hsum
    have hi : q.mass i = 0 := le_antisymm (by linarith) (q.nonneg i)
    simpa [pointMass, hij] using hi

theorem eq_pointMass_of_largestMass_one (q : DiscreteLaw) (hq : largestMass q = 1) :
    q = pointMass (largestIndex q) := by
  apply q.eq_pointMass_of_mass_one
  rw [← largestMass_eq_selected, hq]

@[simp] theorem roundedScale_radius_one (q : DiscreteLaw) : roundedScale q 1 = 0 := by
  simp [roundedScale, complexityScale]

theorem roundedScale_point_branch (q : DiscreteLaw) (hq : largestMass q = 1)
    {ε : ℝ} (hε : ε < 1) : roundedScale q ε = ⌈1 / ε⌉₊ := by
  simp [roundedScale, complexityScale, ne_of_lt hε, hq]

theorem point_branch_upper (q : DiscreteLaw) (hq : largestMass q = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    HasIdentityTest q ε (roundedScale q ε) := by
  rw [roundedScale_point_branch q hq hε1]
  rw [eq_pointMass_of_largestMass_one q hq]
  exact pointMass_hasIdentityTest_ceil _ hε0 hε1

theorem point_branch_lower (q : DiscreteLaw) (hq : largestMass q = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (n : ℕ)
    (h : HasIdentityTest q ε n) : (1 / 4 : ℝ) * roundedScale q ε ≤ n := by
  have hp := eq_pointMass_of_largestMass_one q hq
  have hn := pointMass_ceil_lower_bound (largestIndex q) hε0 hε1 n (hp ▸ h)
  rw [roundedScale_point_branch q hq hε1]
  have hn' : (⌈1 / ε⌉₊ : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Original uniform comparison for every q in the radius-one or point-mass
branches.  The remaining branches are not asserted by this theorem. -/
theorem degenerate_branches_characterization (q : DiscreteLaw) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hbranch : ε = 1 ∨ largestMass q = 1) :
    (∀ n : ℕ, HasIdentityTest q ε n →
      (1 / 4 : ℝ) * roundedScale q ε ≤ n) ∧
    (∃ n : ℕ, HasIdentityTest q ε n ∧ (n : ℝ) ≤ roundedScale q ε) := by
  by_cases he : ε = 1
  · subst ε
    constructor
    · intro n _
      simp
    · exact ⟨0, radius_one_zero_samples q, by simp⟩
  · have hq : largestMass q = 1 := hbranch.resolve_left he
    have he1 : ε < 1 := lt_of_le_of_ne hε1 he
    exact ⟨fun n hn => point_branch_lower q hq hε0 he1 n hn,
      roundedScale q ε, point_branch_upper q hq hε0 he1, le_rfl⟩

end IdentityTesting
