import IdentityTesting.BinaryRationalNormalizationBound

namespace IdentityTesting.BinaryRationalNormalizationMachine
open BinaryArithmetic

def signedFraction (negative : Bool) (m d : ℕ) : ℚ :=
  if negative then -(m : ℚ) / d else (m : ℚ) / d

def outputValue (s : State) : ℚ :=
  signedFraction s.negative (value s.num.quot.out) (value s.den.quot.out)

theorem fraction_reduction (m d : ℕ) (hd : 0 < d) :
    ((m / Nat.gcd m d : ℕ) : ℚ) / (d / Nat.gcd m d : ℕ) = (m : ℚ) / d := by
  let g := Nat.gcd m d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right m hd
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hg
  have hm : m / g * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m d)
  have hden : d / g * g = d := Nat.div_mul_cancel (Nat.gcd_dvd_right m d)
  have hmQ : ((m / g : ℕ) : ℚ) * g = m := by exact_mod_cast hm
  have hdQ : ((d / g : ℕ) : ℚ) * g = d := by exact_mod_cast hden
  change ((m / g : ℕ) : ℚ) / (d / g : ℕ) = (m : ℚ) / d
  rw [← hmQ, ← hdQ, mul_div_mul_right _ _ hgq]

theorem signed_fraction_reduction (sg : Bool) (m d : ℕ) (hd : 0 < d) :
    signedFraction (if (m / Nat.gcd m d).bits = [] then false else sg)
      (m / Nat.gcd m d) (d / Nat.gcd m d) = signedFraction sg m d := by
  have he := fraction_reduction m d hd
  by_cases hz : (m / Nat.gcd m d).bits = []
  · have hq : m / Nat.gcd m d = 0 := by
      have hv := value_bits (m / Nat.gcd m d)
      rw [hz] at hv
      exact hv.symm
    have hm : m = 0 := by
      have h := Nat.div_mul_cancel (Nat.gcd_dvd_left m d)
      rw [hq, Nat.zero_mul] at h
      exact h.symm
    cases sg <;> simp [signedFraction, hz, hq, hm]
  · simp only [hz, ↓reduceIte]
    cases sg <;> simp only [signedFraction, Bool.false_eq_true, ↓reduceIte]
    · exact he
    · simpa only [neg_div] using congrArg Neg.neg he

theorem signedFraction_num_den (sg : Bool) (m d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime m d) :
    (signedFraction sg m d).num.natAbs = m ∧ (signedFraction sg m d).den = d := by
  let z : ℤ := if sg then -(m : ℤ) else m
  have hz : z.natAbs = m := by cases sg <;> simp [z]
  let q : ℚ := ⟨z, d, Nat.ne_of_gt hd, by simpa only [hz] using hcop⟩
  have he : signedFraction sg m d = q := by
    have hq := Rat.num_div_den q
    change (z : ℚ) / d = q at hq
    cases sg <;> simpa [signedFraction, z] using hq
  rw [he]
  exact ⟨hz, rfl⟩

theorem normalization_components (sg : Bool) (m d : ℕ) (hd : 0 < d) :
    m / Nat.gcd m d = (signedFraction sg m d).num.natAbs ∧
      d / Nat.gcd m d = (signedFraction sg m d).den := by
  have hg := Nat.gcd_pos_of_pos_right m hd
  have hc := signedFraction_num_den (if (m / Nat.gcd m d).bits = [] then false else sg)
    (m / Nat.gcd m d) (d / Nat.gcd m d)
    (Nat.div_pos (Nat.gcd_le_right m hd) hg) (Nat.coprime_div_gcd_div_gcd hg)
  rw [signed_fraction_reduction sg m d hd] at hc
  exact ⟨hc.1.symm, hc.2.symm⟩

theorem signedFraction_int (z : ℤ) (d : ℕ) :
    signedFraction (decide (z < 0)) z.natAbs d = (z : ℚ) / d := by
  cases z <;> simp [signedFraction]

/-- Positive reduced denominator, coprime magnitude, canonical zero sign,
exact rational value, and a primitive-action bound all refer to the same run. -/
theorem binary_rational_normalization (sg : Bool) (m d : ℕ) (hd : 0 < d) :
    ∃ steps, let final := advance steps (initial sg m.bits d.bits)
      final.phase = .halt ∧ outputValue final = signedFraction sg m d ∧
      0 < value final.den.quot.out ∧
      Nat.Coprime (value final.num.quot.out) (value final.den.quot.out) ∧
      (value final.num.quot.out = 0 → final.negative = false) ∧
      bitSteps steps (initial sg m.bits d.bits) ≤ 9000 * (m.size + d.size + 1) ^ 3 := by
  obtain ⟨steps, rn, rd, hs, he⟩ := normalization_run sg m d hd
  refine ⟨steps, ?_⟩
  dsimp only
  rw [show advance steps _ = _ from he]
  have hg := Nat.gcd_pos_of_pos_right m hd
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [outputValue, terminal, BinaryDivisionMachine.terminal, value_bits] using
      signed_fraction_reduction sg m d hd
  · simpa only [terminal, BinaryDivisionMachine.terminal, value_bits] using
      Nat.div_pos (Nat.gcd_le_right m hd) hg
  · simpa only [terminal, BinaryDivisionMachine.terminal, value_bits] using
      Nat.coprime_div_gcd_div_gcd hg
  · simp only [terminal, BinaryDivisionMachine.terminal, value_bits]
    intro hzero
    simp [hzero]
  · have hc := bitSteps_le steps (initial sg m.bits d.bits)
    nlinarith

theorem binary_integer_fraction_machine (z : ℤ) (d : ℕ) (hd : 0 < d) :
    ∃ steps, let final := advance steps (initial (decide (z < 0)) z.natAbs.bits d.bits)
      final.phase = .halt ∧
      final.num.quot.out = (((z : ℚ) / d).num.natAbs).bits ∧
      final.den.quot.out = (((z : ℚ) / d).den).bits ∧
      outputValue final = (z : ℚ) / d ∧
      bitSteps steps (initial (decide (z < 0)) z.natAbs.bits d.bits) ≤
        9000 * (z.natAbs.size + d.size + 1) ^ 3 := by
  obtain ⟨steps, rn, rd, hs, he⟩ := normalization_run (decide (z < 0)) z.natAbs d hd
  have hc := normalization_components (decide (z < 0)) z.natAbs d hd
  rw [signedFraction_int] at hc
  refine ⟨steps, ?_⟩
  dsimp only
  rw [show advance steps _ = _ from he]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · exact congrArg Nat.bits hc.1
  · exact congrArg Nat.bits hc.2
  · simpa only [outputValue, terminal, BinaryDivisionMachine.terminal, value_bits, signedFraction_int] using
      signed_fraction_reduction (decide (z < 0)) z.natAbs d hd
  · have hb := bitSteps_le steps (initial (decide (z < 0)) z.natAbs.bits d.bits)
    nlinarith

end IdentityTesting.BinaryRationalNormalizationMachine
