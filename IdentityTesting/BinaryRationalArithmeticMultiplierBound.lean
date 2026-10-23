import IdentityTesting.BinaryRationalArithmeticMultiplierTransport

namespace IdentityTesting.BinaryRationalArithmeticMultiplier
open BinaryArithmetic BinarySignedWords RationalComputation

theorem output_value_eq (s : State) : (output s).value = BinaryRationalNormalizationMachine.outputValue s.norm := by
  cases h : s.norm.negative <;>
    simp [output,BinaryRationalArithmetic.Word.value,Word.value,signedValue,
      BinaryRationalNormalizationMachine.outputValue,BinaryRationalNormalizationMachine.signedFraction,h]

theorem binary_rational_multiplication_machine (p q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)
      (advance steps s).phase = .halt ∧ (output (advance steps s)).value = p*q ∧
      (output (advance steps s)).numerator.magnitude = (p*q).num.natAbs.bits ∧
      (output (advance steps s)).denominator = (p*q).den.bits ∧
      ((output (advance steps s)).numerator.magnitude = [] → (output (advance steps s)).numerator.negative = false) ∧
      bitSteps steps s ≤ 20000 * (rationalEncodingLength p + rationalEncodingLength q + 1)^3 := by
  let a := decide (p.num < 0)
  let b := decide (q.num < 0)
  let ni := BinarySignedMultiplier.initial a b p.num.natAbs.bits q.num.natAbs.bits
  let di := BinarySignedMultiplier.initial false false p.den.bits q.den.bits
  let r0 := BinaryRationalNormalizationMachine.initial false [] []
  let s0 : State := ⟨.numerator,ni,di,r0,[]⟩
  let m := p.num.natAbs*q.num.natAbs
  let d := p.den*q.den
  obtain ⟨kn,hkn,hnh,hnm,hnv⟩ := BinarySignedMultiplier.run_signed_product a b p.num.natAbs.bits q.num.natAbs.bits
  obtain ⟨kd,hkd,hdh,hdm,hdv⟩ := BinarySignedMultiplier.run_signed_product false false p.den.bits q.den.bits
  let nf := BinarySignedMultiplier.advance kn ni
  let df := BinarySignedMultiplier.advance kd di
  have hnm' : nf.norm.out = m.bits := by simpa [nf,ni,m] using hnm
  have hdm' : df.norm.out = d.bits := by simpa [df,di,d] using hdm
  have hnv' : signedValue nf.negative m = p.num*q.num := by
    change signedValue nf.negative (value nf.norm.out) = _ at hnv
    rw [hnm',value_bits] at hnv
    simpa only [a,b,value_bits,signedValue_int] using hnv
  obtain ⟨jn,hjn,hjnr⟩ := forward_numerator s0 ni kn hnh
  have hnum : Runs s0 jn ⟨.denominator,nf,di,r0,[]⟩ := hjnr
  obtain ⟨jd,hjd,hjdr⟩ := forward_denominator ⟨.denominator,nf,di,r0,[]⟩ di kd hdh
  have hden : Runs ⟨.denominator,nf,di,r0,[]⟩ jd
      ⟨.numCollect,nf,df,BinaryRationalNormalizationMachine.initial nf.negative [] [],[]⟩ := hjdr
  have hdpos : 0 < d := Nat.mul_pos p.den_pos q.den_pos
  obtain ⟨kr,rn,rd,hkr,hkrr⟩ := normalize_outputs nf df m d hnm' hdm' hdpos
  have hr := (hnum.trans hden).trans hkrr
  have hfrac : BinaryRationalNormalizationMachine.signedFraction nf.negative m d = p*q := by
    have hc : ((signedValue nf.negative m : ℤ) : ℚ) = (p.num:ℚ)*(q.num:ℚ) := by exact_mod_cast hnv'
    have hf : BinaryRationalNormalizationMachine.signedFraction nf.negative m d =
        ((signedValue nf.negative m : ℤ):ℚ) / d := by
      cases hs : nf.negative <;> simp [BinaryRationalNormalizationMachine.signedFraction,signedValue,hs]
    rw [hf,hc]
    simp only [d,Nat.cast_mul,mul_div_mul_comm,Rat.num_div_den]
  have hc := BinaryRationalNormalizationMachine.normalization_components nf.negative m d hdpos
  rw [hfrac] at hc
  refine ⟨jn+jd+kr,?_,?_,?_,?_,?_,?_⟩
  · change (advance _ s0).phase = _
    rw [hr]
  · change (output (advance _ s0)).value = _
    rw [output_value_eq,hr]
    simpa only [BinaryRationalNormalizationMachine.outputValue,
      BinaryRationalNormalizationMachine.terminal,BinaryDivisionMachine.terminal,value_bits,hfrac] using
      BinaryRationalNormalizationMachine.signed_fraction_reduction nf.negative m d hdpos
  · change (advance _ s0).norm.num.quot.out = _
    rw [hr]
    exact congrArg Nat.bits hc.1
  · change (advance _ s0).norm.den.quot.out = _
    rw [hr]
    exact congrArg Nat.bits hc.2
  · change (advance _ s0).norm.num.quot.out = [] → (advance _ s0).norm.negative = false
    rw [hr]
    simp only [BinaryRationalNormalizationMachine.terminal,BinaryDivisionMachine.terminal]
    intro hz
    simp [hz]
  · have hb := bitSteps_le (jn+jd+kr) s0
    change bitSteps (jn+jd+kr) s0 ≤ _
    simp only [Nat.size_eq_bits_len] at hkn hkd
    have hm := nat_size_mul_le p.num.natAbs q.num.natAbs
    have hd := nat_size_mul_le p.den q.den
    change m.size ≤ p.num.natAbs.size+q.num.natAbs.size at hm
    change d.size ≤ p.den.size+q.den.size at hd
    let S := rationalEncodingLength p+rationalEncodingLength q+1
    have hmS : m.size+d.size+1 ≤ S := by
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]
      omega
    have hcub := Nat.pow_le_pow_left hmS 3
    have hnp : p.num.natAbs.size ≤ S := by dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hnq : p.num.natAbs.size+q.num.natAbs.size+1 ≤ S := by dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hdp : p.den.size ≤ S := by dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hdq : p.den.size+q.den.size+1 ≤ S := by dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hnprod := Nat.mul_le_mul hnp hnq
    have hdprod := Nat.mul_le_mul hdp hdq
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hSS : S*S ≤ S^3 := by nlinarith only [Nat.mul_le_mul_left (S*S) hS]
    have hS2 : S ≤ S*S := by nlinarith only [hS]
    have hS3 : S ≤ S^3 := hS2.trans hSS
    have hnBound : kn ≤ 20*(S*S)+4*S+9 := by nlinarith only [hkn,hnprod,hnq]
    have hdBound : kd ≤ 20*(S*S)+4*S+9 := by nlinarith only [hkd,hdprod,hdq]
    have hrBound : kr ≤ 1002*S^3+5 := by nlinarith only [hkr,hmS,hcub,hS3]
    change bitSteps (jn+jd+kr) s0 ≤ 20000*S^3
    nlinarith only [hb,hjn,hjd,hnBound,hdBound,hrBound,hSS,hS3,hS]

end IdentityTesting.BinaryRationalArithmeticMultiplier
