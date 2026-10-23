import IdentityTesting.CountableCharacterizationRealScale
import IdentityTesting.PointMassExact

/-! The minimum natural sample count in the original strict-alternative model.
The value on inputs admitting no test is zero; every theorem about its minimum
semantics establishes existence, including all manuscript radii. -/

noncomputable section
namespace IdentityTesting

def minimumSampleComplexity (q : DiscreteLaw) (ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, HasIdentityTest q ε n then Nat.find h else 0

theorem minimumSampleComplexity_isLeast_of_exists (q : DiscreteLaw) (ε : ℝ)
    (h : ∃ n, HasIdentityTest q ε n) :
    IsLeast {n : ℕ | HasIdentityTest q ε n} (minimumSampleComplexity q ε) := by
  classical
  rw [minimumSampleComplexity, dif_pos h]
  exact ⟨Nat.find_spec h, fun _ hn => Nat.find_min' h hn⟩

theorem minimumSampleComplexity_isLeast (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    IsLeast {n : ℕ | HasIdentityTest q ε n} (minimumSampleComplexity q ε) := by
  obtain ⟨n, hn, _⟩ := countable_characterization_upper q ε hε0 hε1
  exact minimumSampleComplexity_isLeast_of_exists q ε ⟨n, hn⟩

theorem minimumSampleComplexity_eq_of_isLeast (q : DiscreteLaw) (ε : ℝ)
    {n : ℕ} (hn : IsLeast {n : ℕ | HasIdentityTest q ε n} n) :
    minimumSampleComplexity q ε = n := by
  have hm := minimumSampleComplexity_isLeast_of_exists q ε ⟨n, hn.1⟩
  exact le_antisymm (hm.2 hn.1) (hn.2 hm.1)

theorem minimumSampleComplexity_at_one (q : DiscreteLaw) :
    minimumSampleComplexity q 1 = 0 := by
  apply minimumSampleComplexity_eq_of_isLeast
  exact ⟨radius_one_zero_samples q, fun _ _ => Nat.zero_le _⟩

theorem minimumSampleComplexity_point_reference (q : DiscreteLaw)
    (hq : largestMass q = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    minimumSampleComplexity q ε = ⌈Real.log 2 / (-Real.log (1 - ε))⌉₊ :=
  minimumSampleComplexity_eq_of_isLeast q ε
    (point_reference_exact_minimum q hq hε0 hε1)

theorem minimumSampleComplexity_pos (q : DiscreteLaw) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < minimumSampleComplexity q ε := by
  have hm := minimumSampleComplexity_isLeast q hε0 hε1.le
  have h := countable_characterization_realScale
  obtain ⟨c, C, hc, _, hbound⟩ := h
  have hl := (hbound q ε hε0 hε1.le).1 _ hm.1
  have hscale := complexityScale_ge_one q hε0 hε1
  have hp : 0 < (minimumSampleComplexity q ε : ℝ) := by nlinarith
  exact_mod_cast hp

/-- The manuscript's literal minimum-sample formulation, for every countable
reference, including the zero-sample radius-one endpoint. -/
theorem minimumSampleComplexity_characterization :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ (q : DiscreteLaw) (ε : ℝ), 0 < ε → ε ≤ 1 →
        c * complexityScale q ε ≤ (minimumSampleComplexity q ε : ℝ) ∧
        (minimumSampleComplexity q ε : ℝ) ≤ C * complexityScale q ε := by
  obtain ⟨c, C, hc, hcC, h⟩ := countable_characterization_realScale
  refine ⟨c, C, hc, hcC, ?_⟩
  intro q ε hε0 hε1
  have hm := minimumSampleComplexity_isLeast q hε0 hε1
  obtain ⟨hl, n, hn, hu⟩ := h q ε hε0 hε1
  refine ⟨hl _ hm.1, ?_⟩
  exact (show (minimumSampleComplexity q ε : ℝ) ≤ (n : ℝ) by
    exact_mod_cast hm.2 hn).trans hu

end IdentityTesting
