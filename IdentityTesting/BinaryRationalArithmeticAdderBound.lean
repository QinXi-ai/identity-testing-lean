import IdentityTesting.BinaryRationalArithmeticAdderAssembly

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic BinarySignedWords RationalComputation

theorem binary_rational_addition_machine (p q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      (advance steps s).phase = .halt ∧ (output (advance steps s)).value = p+q ∧
      (output (advance steps s)).numerator.magnitude = (p+q).num.natAbs.bits ∧
      (output (advance steps s)).denominator = (p+q).den.bits ∧
      ((output (advance steps s)).numerator.magnitude = [] → (output (advance steps s)).numerator.negative = false) ∧
      bitSteps steps s ≤ 1300000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 := by
  obtain ⟨steps,n,d,r,a,rn,rd,hs,hav,ham,hr⟩ := addition_run p q
  let z : ℤ := p.num*q.den+q.num*p.den
  let v := p.den*q.den
  have hv : 0 < v := Nat.mul_pos p.den_pos q.den_pos
  have hz : signedValue a.negative z.natAbs = z := by
    rw [ham,value_bits] at hav
    exact hav
  have hfrac : BinaryRationalNormalizationMachine.signedFraction a.negative z.natAbs v = p+q := by
    have hf : BinaryRationalNormalizationMachine.signedFraction a.negative z.natAbs v =
        ((signedValue a.negative z.natAbs : ℤ):ℚ) / v := by
      cases hsg : a.negative <;> simp [BinaryRationalNormalizationMachine.signedFraction,signedValue,hsg]
    rw [hf,hz]
    rw [Rat.add_num_den,Rat.divInt_eq_div]
    dsimp [z,v]
    push_cast
    ring
  have hc := BinaryRationalNormalizationMachine.normalization_components a.negative z.natAbs v hv
  rw [hfrac] at hc
  refine ⟨steps,?_,?_,?_,?_,?_,?_⟩
  · rw [hr]
  · change (BinaryRationalArithmeticMultiplier.output (advance _ _).base).value = _
    rw [BinaryRationalArithmeticMultiplier.output_value_eq,hr]
    simpa only [BinaryRationalNormalizationMachine.outputValue,
      BinaryRationalNormalizationMachine.terminal,BinaryDivisionMachine.terminal,value_bits,hfrac] using
      BinaryRationalNormalizationMachine.signed_fraction_reduction a.negative z.natAbs v hv
  · change (advance _ _).base.norm.num.quot.out = _
    rw [hr]
    exact congrArg Nat.bits hc.1
  · change (advance _ _).base.norm.den.quot.out = _
    rw [hr]
    exact congrArg Nat.bits hc.2
  · change (advance _ _).base.norm.num.quot.out = [] → (advance _ _).base.norm.negative = false
    rw [hr]
    simp only [BinaryRationalNormalizationMachine.terminal,BinaryDivisionMachine.terminal]
    intro hz
    simp [hz]
  · have hb := bitSteps_le steps (initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q))
    omega

end IdentityTesting.BinaryRationalArithmeticAdder
