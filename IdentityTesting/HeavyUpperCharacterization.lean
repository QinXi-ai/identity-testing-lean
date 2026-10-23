import IdentityTesting.HeavyUpperFinite
import IdentityTesting.HeavyExteriorUpperBound
import IdentityTesting.CountableUpperTransfer

/-! The complete heavy upper branch, including the exterior minimum and the
actual transfer from finite references to arbitrary countable references. -/
noncomputable section
namespace IdentityTesting
open FiniteTesting FiniteAllocationUpper

theorem HasIdentityTest.mono_radius {q : DiscreteLaw} {e ε : ℝ} {n : ℕ}
    (ht : HasIdentityTest q e n) (h : e ≤ ε) : HasIdentityTest q ε n := by
  obtain ⟨test, hnull, halt⟩ := ht
  exact ⟨test, hnull, fun p hp => halt p (h.trans_lt hp)⟩

theorem finite_largest_mass_attained {k : ℕ} (q : Probability (Fin k)) :
    ∃ j : Fin k, q.mass j = largestMass (extendFiniteLaw q) := by
  have hpos := largestMass_pos (extendFiniteLaw q)
  have hj : largestIndex (extendFiniteLaw q) < k := by
    by_contra hj
    rw [largestMass_eq_selected, extendFiniteLaw_mass_of_not_lt q _ hj] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨⟨largestIndex (extendFiniteLaw q), hj⟩, ?_⟩
  rw [largestMass_eq_selected]
  exact (extendFiniteLaw_mass_val q _).symm

/-- Every finite heavy reference, with zero masses allowed and with the original
infinite observation alphabet, admits the test at its exact piecewise scale. -/
theorem finite_heavy_branch_upper {k : ℕ} (q : Probability (Fin k))
    (hh : (3 : ℝ) / 4 < largestMass (extendFiniteLaw q))
    (hq : largestMass (extendFiniteLaw q) < 1) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, HasIdentityTest (extendFiniteLaw q) ε n ∧
      (n : ℝ) ≤ (10 : ℝ) ^ 41 * (roundedScale (extendFiniteLaw q) ε : ℝ) := by
  let Q := extendFiniteLaw q
  let R := 1 - largestMass Q
  change (3 : ℝ) / 4 < largestMass Q at hh
  change largestMass Q < 1 at hq
  have hR : 0 < R := sub_pos.mpr hq
  have hround : 0 ≤ (roundedScale Q ε : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ coarseSampleConstant + 10004 := by norm_num [coarseSampleConstant]
  have hCmax : coarseSampleConstant + 10004 ≤ (10 : ℝ) ^ 41 := by
    norm_num [coarseSampleConstant]
  have hcmax : (1000001 : ℝ) ≤ (10 : ℝ) ^ 41 := by norm_num
  by_cases heR : ε ≤ R
  · change ε ≤ 1 - largestMass Q at heR
    obtain ⟨n, ht, hn⟩ := HeavyUpper.finite_heavy_upper_bound_with_zeros q hh.le hq hε0 heR
    have hs : complexityScale Q ε = heavyRoot Q ε := by
      simp only [complexityScale, ne_of_lt hε1, ne_of_lt hq, hh, heR,
        if_false, if_true]
    have hceil : heavyRoot Q ε ≤ (roundedScale Q ε : ℝ) := by
      rw [← hs]
      exact Nat.le_ceil _
    exact ⟨n, ht, hn.trans ((mul_le_mul_of_nonneg_left hceil hC).trans
      (mul_le_mul_of_nonneg_right hCmax hround))⟩
  · have heR' : R < ε := lt_of_not_ge heR
    change ¬ ε ≤ 1 - largestMass Q at heR
    let K := R / (ε - R) ^ 2 + 1 / (ε - R)
    have hs : complexityScale Q ε = min (heavyRoot Q R) K := by
      simp only [complexityScale, ne_of_lt hε1, ne_of_lt hq, hh, heR,
        if_false, if_true]
      rfl
    by_cases hmin : heavyRoot Q R ≤ K
    · obtain ⟨n, ht, hn⟩ := HeavyUpper.finite_heavy_upper_bound_with_zeros q hh.le hq hR le_rfl
      have hceil : heavyRoot Q R ≤ (roundedScale Q ε : ℝ) := by
        rw [min_eq_left hmin] at hs
        rw [← hs]
        exact Nat.le_ceil _
      exact ⟨n, ht.mono_radius heR'.le, hn.trans
        ((mul_le_mul_of_nonneg_left hceil hC).trans
          (mul_le_mul_of_nonneg_right hCmax hround))⟩
    · obtain ⟨j, hj⟩ := finite_largest_mass_attained q
      have hradius : 1 - q.mass j + (ε - R) = ε := by
        rw [hj]
        dsimp only [R, Q]
        ring
      obtain ⟨n, ht, hn⟩ := HeavyExteriorTesting.finite_exterior_count_upper q j (ε - R)
        (sub_pos.mpr heR') (by rw [hradius]; exact hε1)
      rw [hradius] at ht
      have hceil : K ≤ (roundedScale Q ε : ℝ) := by
        rw [min_eq_right (le_of_not_ge hmin)] at hs
        rw [← hs]
        exact Nat.le_ceil _
      have hn' : (n : ℝ) ≤ 1000001 * K := by
        simpa only [hj, K, R, Q] using hn
      exact ⟨n, ht, hn'.trans ((mul_le_mul_of_nonneg_left hceil (by norm_num)).trans
        (mul_le_mul_of_nonneg_right hcmax hround))⟩

theorem countable_heavy_branch_upper (q : DiscreteLaw)
    (hh : (3 : ℝ) / 4 < largestMass q) (hq : largestMass q < 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ n : ℕ, HasIdentityTest q ε n ∧
      (n : ℝ) ≤ (2 * (10 : ℝ) ^ 41) * (roundedScale q ε : ℝ) := by
  apply countable_heavy_upper_of_finite_heavy_upper (by positivity) ?_ q hh hq ε hε0 hε1
  intro k p e hp hp1 he0 he1
  exact finite_heavy_branch_upper p hp hp1 e he0 he1

end IdentityTesting
