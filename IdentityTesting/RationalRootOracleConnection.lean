import IdentityTesting.RationalRootSearch
import IdentityTesting.RationalOracleSearch

/-! Certified approximate evaluations imply valid decisions in the rational
root search. The quantitative time separation is an explicit caller obligation. -/
namespace IdentityTesting.RationalComputation
noncomputable section

theorem rootBracket_of_oracle_separation
    (f : ℝ → ℝ) (evaluate : ℚ → ℚ × ℚ) (e L U σ : ℚ) (root η : ℝ)
    (hanti : StrictAntiOn f (Set.Ioi 0))
    (hroot : 0 < root) (heq : f root = (e : ℝ))
    (hL : 0 < L) (hLr : (L : ℝ) ≤ root) (hrU : root ≤ (U : ℝ))
    (hη0 : 0 ≤ η) (hη1 : η < 1) (he : 0 < e)
    (hσ : (σ : ℝ) ≤ η * (e : ℝ))
    (horacle : ∀ m : ℚ, L ≤ m → m ≤ U → OracleIntervalValid (f m) σ (evaluate m))
    (hsep : ∀ m : ℚ, L ≤ m → m ≤ U →
      f m ≤ (1 - η) * f ((3 * m / 4 : ℚ) : ℝ) ∧
      f ((3 * m / 2 : ℚ) : ℝ) ≤ (1 - η) * f m) :
    RootIntervalValid root (rootBracket evaluate e L U) := by
  have hcompareL (x : ℝ) (hx : 0 < x) (hf : (e : ℝ) ≤ f x) : x ≤ root := by
    by_contra h
    have hh := hanti hroot hx (lt_of_not_ge h)
    rw [heq] at hh
    exact (not_lt_of_ge hf) hh
  have hcompareU (x : ℝ) (hx : 0 < x) (hf : f x ≤ (e : ℝ)) : root ≤ x := by
    by_contra h
    have hh := hanti hx hroot (lt_of_not_ge h)
    rw [heq] at hh
    exact (not_lt_of_ge hf) hh
  apply rootBracket_spec evaluate e L U root hL hLr hrU
  · intro m hmL hmU h
    have hm : (0 : ℝ) < m := by exact_mod_cast hL.trans_le hmL
    exact hcompareL m hm ((by exact_mod_cast h : (e : ℝ) < (evaluate m).1).le.trans
      (horacle m hmL hmU).1)
  · intro m hmL hmU h
    have hm : (0 : ℝ) < m := by exact_mod_cast hL.trans_le hmL
    exact hcompareU m hm ((horacle m hmL hmU).2.1.trans
      (by exact_mod_cast h : ((evaluate m).2 : ℝ) < e).le)
  · intro m hmL hmU hl hu
    obtain ⟨ha, hb, hw⟩ := horacle m hmL hmU
    have hlR : ((evaluate m).1 : ℝ) ≤ e := by exact_mod_cast hl
    have huR : (e : ℝ) ≤ (evaluate m).2 := by exact_mod_cast hu
    have hwR : ((evaluate m).2 : ℝ) - (evaluate m).1 ≤ σ := by exact_mod_cast hw
    obtain ⟨hsmall, hlarge⟩ := hsep m hmL hmU
    have hm : (0 : ℝ) < m := by exact_mod_cast hL.trans_le hmL
    have heR : (0 : ℝ) < e := by exact_mod_cast he
    have hη : 0 < 1 - η := sub_pos.mpr hη1
    constructor
    · apply hcompareL _ (by push_cast; positivity)
      have hf : (1 - η) * (e : ℝ) ≤ (1 - η) * f ((3 * m / 4 : ℚ) : ℝ) := by
        nlinarith only [ha, huR, hwR, hσ, hsmall]
      exact (mul_le_mul_iff_right₀ hη).mp hf
    · apply hcompareU _ (by push_cast; positivity)
      have hfm : f m ≤ (e : ℝ) + σ := by linarith only [hb, hlR, hwR]
      have hmul := mul_le_mul_of_nonneg_left hfm hη.le
      have hσnonneg : (0 : ℝ) ≤ σ := by linarith only [ha, hb, hwR]
      nlinarith only [hlarge, hmul, hσ, mul_nonneg hη0 hσnonneg]

end
end IdentityTesting.RationalComputation
