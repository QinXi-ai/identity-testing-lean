import IdentityTesting.RationalRootSearch

namespace IdentityTesting.RationalComputation

def intervalMin (I : ℚ × ℚ) (b : ℚ) : ℚ × ℚ := (min I.1 b, min I.2 b)

noncomputable section

def ScaleIntervalValid (value : ℝ) (I : ℚ × ℚ) : Prop :=
  0 ≤ I.1 ∧ (I.1 : ℝ) ≤ value ∧ value ≤ (I.2 : ℝ) ∧ I.2 ≤ 2 * I.1

theorem RootIntervalValid.to_scale {value : ℝ} {I : ℚ × ℚ}
    (h : RootIntervalValid value I) : ScaleIntervalValid value I :=
  ⟨h.1.le, h.2⟩

theorem scaleInterval_singleton (b : ℚ) (hb : 0 ≤ b) :
    ScaleIntervalValid (b : ℝ) (b, b) := by
  exact ⟨hb, le_rfl, le_rfl, by dsimp; linarith⟩

theorem rootInterval_singleton (b : ℚ) (hb : 0 < b) :
    RootIntervalValid (b : ℝ) (b, b) := by
  exact ⟨hb, le_rfl, le_rfl, by dsimp; linarith⟩

theorem rootInterval_min {value : ℝ} {I : ℚ × ℚ} (b : ℚ)
    (h : RootIntervalValid value I) (hb : 0 < b) :
    RootIntervalValid (min value (b : ℝ)) (intervalMin I b) := by
  refine ⟨lt_min h.1 hb, ?_, ?_, ?_⟩
  · change ((min I.1 b : ℚ) : ℝ) ≤ _
    rw [Rat.cast_min]
    exact min_le_min h.2.1 le_rfl
  · change _ ≤ ((min I.2 b : ℚ) : ℝ)
    rw [Rat.cast_min]
    exact min_le_min h.2.2.1 le_rfl
  · change min I.2 b ≤ 2 * min I.1 b
    rcases le_total I.1 b with hh | hh
    · rw [min_eq_left hh]
      exact (min_le_left _ _).trans h.2.2.2
    · rw [min_eq_right hh]
      exact (min_le_right _ _).trans (by linarith)

end
end IdentityTesting.RationalComputation
