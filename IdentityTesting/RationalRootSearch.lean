import IdentityTesting.RationalAllocationOracleInputs

/-! Rational root search with certified strict updates and an original-radius
ambiguity window. Concrete callers must supply those certificates from actual
function evaluations; the executable search itself uses rational arithmetic. -/
namespace IdentityTesting.RationalComputation

def rootSearch (evaluate : ℚ → ℚ × ℚ) (e : ℚ) : ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, l, u => (l, u)
  | n + 1, l, u =>
      if u ≤ 2 * l then (l, u)
      else
        let m := (l + u) / 2
        let I := evaluate m
        if e < I.1 then rootSearch evaluate e n m u
        else if I.2 < e then rootSearch evaluate e n l m
        else (max l (3 * m / 4), min u (3 * m / 2))

def rootBracket (evaluate : ℚ → ℚ × ℚ) (e L U : ℚ) : ℚ × ℚ :=
  rootSearch evaluate e (oracleDyadicPrecision (U - L) L) L U

noncomputable section

def RootIntervalValid (root : ℝ) (I : ℚ × ℚ) : Prop :=
  0 < I.1 ∧ (I.1 : ℝ) ≤ root ∧ root ≤ (I.2 : ℝ) ∧ I.2 ≤ 2 * I.1

theorem rootSearch_spec (evaluate : ℚ → ℚ × ℚ) (e L U : ℚ) (root : ℝ)
    (hleft : ∀ m : ℚ, L ≤ m → m ≤ U → e < (evaluate m).1 → (m : ℝ) ≤ root)
    (hright : ∀ m : ℚ, L ≤ m → m ≤ U → (evaluate m).2 < e → root ≤ (m : ℝ))
    (hambiguous : ∀ m : ℚ, L ≤ m → m ≤ U → (evaluate m).1 ≤ e → e ≤ (evaluate m).2 →
      ((3 * m / 4 : ℚ) : ℝ) ≤ root ∧ root ≤ ((3 * m / 2 : ℚ) : ℝ))
    (n : ℕ) (l u : ℚ) (hl : 0 < l) (hLl : L ≤ l) (huU : u ≤ U)
    (hlr : (l : ℝ) ≤ root) (hru : root ≤ (u : ℝ))
    (hfuel : u - l ≤ 2 ^ n * l) :
    RootIntervalValid root (rootSearch evaluate e n l u) := by
  induction n generalizing l u with
  | zero =>
      change RootIntervalValid root (l, u)
      refine ⟨hl, hlr, hru, ?_⟩
      simp only [pow_zero, one_mul] at hfuel
      linarith only [hfuel]
  | succ n ih =>
      have hlu : l ≤ u := by exact_mod_cast hlr.trans hru
      have hlm : l ≤ (l + u) / 2 := by linarith
      have hmu : (l + u) / 2 ≤ u := by linarith
      have hLm := hLl.trans hlm
      have hmU := hmu.trans huU
      have hnext : u - (l + u) / 2 ≤ 2 ^ n * ((l + u) / 2) := by
        have hm := mul_le_mul_of_nonneg_left hlm (by positivity : (0 : ℚ) ≤ 2 ^ n)
        rw [pow_succ] at hfuel
        nlinarith only [hfuel, hm]
      have hprev : (l + u) / 2 - l ≤ 2 ^ n * l := by
        rw [pow_succ] at hfuel
        nlinarith only [hfuel]
      simp only [rootSearch]
      split_ifs with hn hlo hhi
      · exact ⟨hl, hlr, hru, hn⟩
      · exact ih _ _ (hl.trans_le hlm) hLm huU (hleft _ hLm hmU hlo) hru hnext
      · exact ih _ _ hl hLl hmU hlr (hright _ hLm hmU hhi) hprev
      · obtain ⟨hwinL, hwinU⟩ := hambiguous _ hLm hmU (le_of_not_gt hlo) (le_of_not_gt hhi)
        refine ⟨hl.trans_le (le_max_left _ _), ?_, ?_, ?_⟩
        · rw [Rat.cast_max]
          exact max_le hlr hwinL
        · rw [Rat.cast_min]
          exact le_min hru hwinU
        · have hu' := min_le_right u (3 * ((l + u) / 2) / 2)
          have hl' := le_max_right l (3 * ((l + u) / 2) / 4)
          linarith only [hu', hl']

theorem rootBracket_spec (evaluate : ℚ → ℚ × ℚ) (e L U : ℚ) (root : ℝ)
    (hL : 0 < L) (hLr : (L : ℝ) ≤ root) (hrU : root ≤ (U : ℝ))
    (hleft : ∀ m : ℚ, L ≤ m → m ≤ U → e < (evaluate m).1 → (m : ℝ) ≤ root)
    (hright : ∀ m : ℚ, L ≤ m → m ≤ U → (evaluate m).2 < e → root ≤ (m : ℝ))
    (hambiguous : ∀ m : ℚ, L ≤ m → m ≤ U → (evaluate m).1 ≤ e → e ≤ (evaluate m).2 →
      ((3 * m / 4 : ℚ) : ℝ) ≤ root ∧ root ≤ ((3 * m / 2 : ℚ) : ℝ)) :
    RootIntervalValid root (rootBracket evaluate e L U) := by
  apply rootSearch_spec evaluate e L U root hleft hright hambiguous _ L U hL le_rfl le_rfl hLr hrU
  have h := oracleDyadicPrecision_spec (U - L) L hL
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ oracleDyadicPrecision (U - L) L)).mp at h
  simpa only [mul_comm] using h

end
end IdentityTesting.RationalComputation
