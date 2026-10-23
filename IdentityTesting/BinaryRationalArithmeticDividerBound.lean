import IdentityTesting.BinaryRationalArithmeticDivider

namespace IdentityTesting.BinaryRationalArithmeticDivider
open BinaryArithmetic BinarySignedWords RationalComputation

theorem binary_rational_division_machine (p q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      ((advance steps s).phase = .halt ∨ (advance steps s).phase = .zeroHalt) ∧
      (output (advance steps s)).value = p/q ∧
      (output (advance steps s)).numerator.magnitude = (p/q).num.natAbs.bits ∧
      (output (advance steps s)).denominator = (p/q).den.bits ∧
      ((output (advance steps s)).numerator.magnitude = [] → (output (advance steps s)).numerator.negative = false) ∧
      bitSteps steps s ≤ 50000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  by_cases hq : q = 0
  · subst q
    let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode 0)
    have htest : s.core.den.mul.shifted = [] := by
      change (BinaryRationalArithmetic.encode (0:ℚ)).numerator.magnitude = []
      simp [BinaryRationalArithmetic.encode,BinarySignedWords.encode]
    have hfirst : step s = {s with phase := .zeroWrite} := by
      change (if s.core.den.mul.shifted = [] then _ else _) = _
      rw [if_pos htest]
    have hw : advance 2 s = {s with phase := .zeroHalt, zeroDen := [true]} := by
      rw [advance,hfirst]
      rfl
    refine ⟨2,?_,?_,?_,?_,?_,?_⟩
    · exact Or.inr (congrArg State.phase hw)
    · change (output (advance 2 s)).value = _
      rw [hw]
      simp [output,BinaryRationalArithmetic.Word.value,Word.value,signedValue,value,htest]
    · change (output (advance 2 s)).numerator.magnitude = _
      rw [hw]
      simp [output,htest]
    · change (output (advance 2 s)).denominator = _
      rw [hw]
      simp [output,htest]
    · change (output (advance 2 s)).numerator.magnitude = [] → (output (advance 2 s)).numerator.negative = false
      rw [hw]
      simp [output,htest]
    · have hb : bitSteps 2 s = 4 := by
        rw [bitSteps,hfirst]
        rfl
      change bitSteps 2 s ≤ _
      rw [hb]
      have h : 0 < (rationalEncodingLength p+rationalEncodingLength 0+1)^3 := by positivity
      omega
  · have hbits : q.num.natAbs.bits ≠ [] := by
      intro hz
      have hh := congrArg value hz
      simp only [value_bits,value] at hh
      exact hq (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp hh))
    have hl : reciprocalLayout (BinaryRationalArithmetic.encode q) = BinaryRationalArithmetic.encode q⁻¹ :=
      (BinaryRationalArithmetic.inverse_encoding q hq).symm
    let c := BinaryRationalArithmeticMultiplier.initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q⁻¹)
    let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
    have hi : s.core = c := by dsimp [s,initial,c]; rw [hl]
    have ht : s.core.den.mul.shifted ≠ [] := hbits
    have hs : step s = ⟨.multiplying,c,[]⟩ := by
      change (if s.core.den.mul.shifted = [] then _ else _) = _
      rw [if_neg ht]
      change ({phase := .multiplying,core := s.core,zeroDen := []} : State) = _
      rw [hi]
    obtain ⟨k,hh,hv,hm,hd,hz,hb⟩ := BinaryRationalArithmeticMultiplier.binary_rational_multiplication_machine p q⁻¹
    obtain ⟨j,hj,hr,hcost⟩ := forward c k hh
    have hw : advance (j+1) s = ⟨.halt,BinaryRationalArithmeticMultiplier.advance k c,[]⟩ := by
      rw [advance,hs,hr]
    refine ⟨j+1,?_,?_,?_,?_,?_,?_⟩
    · exact Or.inl (congrArg State.phase hw)
    · change (output (advance _ s)).value = _
      rw [hw]
      simpa [output,div_eq_mul_inv] using hv
    · change (output (advance _ s)).numerator.magnitude = _
      rw [hw]
      simpa [output,div_eq_mul_inv] using hm
    · change (output (advance _ s)).denominator = _
      rw [hw]
      simpa [output,div_eq_mul_inv] using hd
    · change (output (advance _ s)).numerator.magnitude = [] → (output (advance _ s)).numerator.negative = false
      rw [hw]
      simpa [output] using hz
    · have hstep : (transitionTrace s).length = 2 := rfl
      change bitSteps (j+1) s ≤ _
      rw [bitSteps,hs,hstep]
      rw [rational_inv_encoding q hq] at hb
      change BinaryRationalArithmeticMultiplier.bitSteps k c ≤
        20000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 at hb
      have hone : 0 < (rationalEncodingLength p+rationalEncodingLength q+1)^3 := by positivity
      omega

end IdentityTesting.BinaryRationalArithmeticDivider
