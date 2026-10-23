import IdentityTesting.RationalAlgorithmTraceSearchControl
import IdentityTesting.RationalOracleSearchTrace

/-! Every state of the actual bounded search loop retains a dyadic affine bracket. -/
namespace IdentityTesting.RationalComputation

def OracleSearchControl.Grid (b B : ℚ) (R : ℕ) (s : OracleSearchControl) : Prop :=
  ∃ r ≤ R, ∃ j < 2 ^ r, s.lower = dyadicAffine b B r j ∧
    s.upper = dyadicAffine b B r (j + 1)

theorem OracleSearchControl.step_grid (budget objective : ℚ → ℚ × ℚ) (ζ margin b B : ℚ)
    (R : ℕ) (s : OracleSearchControl) (h : s.Grid b B R) :
    (s.step budget objective ζ margin).Grid b B (R + 1) := by
  obtain ⟨r, hr, j, hj, hl, hu⟩ := h
  have hold : s.Grid b B (R + 1) := ⟨r, by omega, j, hj, hl, hu⟩
  obtain ⟨hl', hu', hm⟩ := dyadicAffine_step b B r j
  have hm' : (s.lower + s.upper) / 2 = dyadicAffine b B (r + 1) (2 * j + 1) := by
    simpa only [hl, hu] using hm
  have hjl : 2 * j < 2 ^ (r + 1) := by rw [pow_succ]; omega
  have hjr : 2 * j + 1 < 2 ^ (r + 1) := by rw [pow_succ]; omega
  by_cases hd : s.done = true
  · simpa only [step, hd, if_true] using hold
  · have hf := Bool.eq_false_iff.mpr hd
    simp only [step, hf, Bool.false_eq_true, if_false]
    split_ifs with hn hlow hhigh
    · exact ⟨r, by omega, j, hj, by simp [finish, hf, hl], by simp [finish, hf, hu]⟩
    · exact ⟨r + 1, by omega, 2 * j + 1, hjr, hm', hu.trans hu'⟩
    · exact ⟨r + 1, by omega, 2 * j, hjl, hl.trans hl', hm'⟩
    · exact ⟨r, by omega, j, hj, hl, hu⟩

theorem OracleSearchControl.loop_grid (budget objective : ℚ → ℚ × ℚ) (ζ margin b B : ℚ)
    (fuel R : ℕ) (s : OracleSearchControl) (h : s.Grid b B R) :
    (loop budget objective ζ margin fuel s).Grid b B (R + fuel) := by
  induction fuel generalizing R s with
  | zero => simpa only [loop, Nat.add_zero] using h
  | succ fuel ih =>
    have hs := step_grid budget objective ζ margin b B R s h
    have hi := ih (R + 1) (s.step budget objective ζ margin) hs
    simpa only [loop, Nat.add_assoc, Nat.add_comm 1 fuel] using hi

theorem OracleSearchControl.grid_encoding (b B : ℚ) (R : ℕ) (s : OracleSearchControl)
    (h : s.Grid b B R) :
    rationalEncodingLength s.lower ≤ 6 * rationalEncodingLength b + 4 * rationalEncodingLength B + 4 * R + 9 ∧
      rationalEncodingLength s.upper ≤ 6 * rationalEncodingLength b + 4 * rationalEncodingLength B + 4 * R + 9 := by
  obtain ⟨r, hr, j, hj, hl, hu⟩ := h
  have h1 := dyadicAffine_encoding_le b B r j hj.le
  have h2 := dyadicAffine_encoding_le b B r (j + 1) (by omega)
  rw [hl, hu]
  constructor <;> omega

theorem OracleSearchControl.initial_grid (b B : ℚ) :
    (OracleSearchControl.mk b B 0 0 0 false).Grid b B 0 := by
  refine ⟨0, le_rfl, 0, by norm_num, ?_, ?_⟩ <;> simp [dyadicAffine]

end IdentityTesting.RationalComputation
