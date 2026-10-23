import IdentityTesting.RationalBisection

/-! Executable rational interval search and its invariant. The generic theorem
is an implementation lemma; actual allocation callers must prove its interval
evaluation and stopping hypotheses from the original input. -/
namespace IdentityTesting.RationalComputation

def oracleSearch (budget objective : ℚ → ℚ × ℚ) (ζ margin : ℚ) :
    ℕ → ℚ → ℚ → ℚ × ℚ
  | 0, l, u => ((objective l).1, (objective u).2)
  | n + 1, l, u =>
      if u - l ≤ ζ * l then ((objective l).1, (objective u).2)
      else
        let m := (l + u) / 2
        let Q := budget m
        if Q.2 < 1 then oracleSearch budget objective ζ margin n m u
        else if 1 < Q.1 then oracleSearch budget objective ζ margin n l m
        else ((objective m).1 - margin, (objective m).2 + margin)

noncomputable section

def OracleIntervalValid (value : ℝ) (σ : ℚ) (I : ℚ × ℚ) : Prop :=
  (I.1 : ℝ) ≤ value ∧ value ≤ (I.2 : ℝ) ∧ I.2 - I.1 ≤ σ

theorem oracleSearch_spec (budget objective : ℚ → ℚ × ℚ)
    (ζ margin σ b B : ℚ) (β value : ℝ) (hζ : 0 ≤ ζ)
    (hleft : ∀ m : ℚ, b ≤ m → m ≤ B → (budget m).2 < 1 → (m : ℝ) ≤ β)
    (hright : ∀ m : ℚ, b ≤ m → m ≤ B → 1 < (budget m).1 → β ≤ (m : ℝ))
    (hnarrow : ∀ l u : ℚ, b ≤ l → u ≤ B → (l : ℝ) ≤ β → β ≤ (u : ℝ) →
      u - l ≤ ζ * l → OracleIntervalValid value σ ((objective l).1, (objective u).2))
    (hambiguous : ∀ m : ℚ, b ≤ m → m ≤ B → (budget m).1 ≤ 1 → 1 ≤ (budget m).2 →
      OracleIntervalValid value σ ((objective m).1 - margin, (objective m).2 + margin))
    (n : ℕ) (l u : ℚ) (hbl : b ≤ l) (huB : u ≤ B)
    (hlβ : (l : ℝ) ≤ β) (hβu : β ≤ (u : ℝ))
    (hfuel : u - l ≤ 2 ^ n * ζ * l) :
    OracleIntervalValid value σ (oracleSearch budget objective ζ margin n l u) := by
  induction n generalizing l u with
  | zero =>
      apply hnarrow l u hbl huB hlβ hβu
      simpa only [pow_zero, one_mul] using hfuel
  | succ n ih =>
      have hlu : l ≤ u := by exact_mod_cast hlβ.trans hβu
      have hlm : l ≤ (l + u) / 2 := by linarith
      have hmu : (l + u) / 2 ≤ u := by linarith
      have hbm : b ≤ (l + u) / 2 := hbl.trans hlm
      have hmB : (l + u) / 2 ≤ B := hmu.trans huB
      have hz : 0 ≤ (2 : ℚ) ^ n * ζ := mul_nonneg (by positivity) hζ
      have hnext : u - (l + u) / 2 ≤ 2 ^ n * ζ * ((l + u) / 2) := by
        have hm := mul_le_mul_of_nonneg_left hlm hz
        rw [pow_succ] at hfuel
        nlinarith only [hfuel, hm]
      have hprev : (l + u) / 2 - l ≤ 2 ^ n * ζ * l := by
        rw [pow_succ] at hfuel
        nlinarith only [hfuel]
      simp only [oracleSearch]
      split_ifs with hn hlow hhigh
      · exact hnarrow l u hbl huB hlβ hβu hn
      · exact ih _ _ hbm huB (hleft _ hbm hmB hlow) hβu hnext
      · exact ih _ _ hbl hmB hlβ (hright _ hbm hmB hhigh) hprev
      · exact hambiguous _ hbm hmB (le_of_not_gt hhigh) (le_of_not_gt hlow)

end
end IdentityTesting.RationalComputation
