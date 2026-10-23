import IdentityTesting.BinaryRationalArithmeticAdderTransport

namespace IdentityTesting.BinaryRationalArithmeticAdder
open BinaryArithmetic BinarySignedWords RationalComputation

theorem addition_run (p q : ℚ) :
    ∃ (steps : ℕ) (n d r : BinarySignedMultiplier.State) (a : BinarySignedAdder.State)
      (rn rd : BinarySubtractorMachine.Registers),
      steps ≤ 100000*(rationalEncodingLength p+rationalEncodingLength q+1)^3 ∧
      signedValue a.negative (value a.norm.out) = p.num*q.den+q.num*p.den ∧
      a.norm.out = (p.num*q.den+q.num*p.den).natAbs.bits ∧
      Runs (initial (BinaryRationalArithmetic.encode p) (BinaryRationalArithmetic.encode q)) steps
        ⟨.halt,
          ⟨.halt,emptied (summed n a),emptied d,
            BinaryRationalNormalizationMachine.terminal a.negative
              (Nat.gcd (p.num*q.den+q.num*p.den).natAbs (p.den*q.den)).bits
              ((p.num*q.den+q.num*p.den).natAbs / Nat.gcd (p.num*q.den+q.num*p.den).natAbs (p.den*q.den)).bits
              ((p.den*q.den) / Nat.gcd (p.num*q.den+q.num*p.den).natAbs (p.den*q.den)).bits rn rd,[]⟩,
          emptied r,{a with norm := {a.norm with out := []}},[]⟩ := by
  let P := BinaryRationalArithmetic.encode p
  let Q := BinaryRationalArithmetic.encode q
  let ni := BinarySignedMultiplier.initial P.numerator.negative false P.numerator.magnitude Q.denominator
  let ri := BinarySignedMultiplier.initial Q.numerator.negative false Q.numerator.magnitude P.denominator
  let di := BinarySignedMultiplier.initial false false P.denominator Q.denominator
  obtain ⟨kn,hkn,hnh,hnm,hnv⟩ := BinarySignedMultiplier.run_signed_product
    P.numerator.negative false P.numerator.magnitude Q.denominator
  obtain ⟨kr,hkr,hrh,hrm,hrv⟩ := BinarySignedMultiplier.run_signed_product
    Q.numerator.negative false Q.numerator.magnitude P.denominator
  obtain ⟨kd,hkd,hdh,hdm,hdv⟩ := BinarySignedMultiplier.run_signed_product
    false false P.denominator Q.denominator
  let n := BinarySignedMultiplier.advance kn ni
  let r := BinarySignedMultiplier.advance kr ri
  let d := BinarySignedMultiplier.advance kd di
  let z : ℤ := p.num*q.den+q.num*p.den
  let v := p.den*q.den
  have hnm' : n.norm.out = (p.num.natAbs*q.den).bits := by
    simpa only [n,ni,P,Q,BinaryRationalArithmetic.encode,BinarySignedWords.encode,value_bits] using hnm
  have hrm' : r.norm.out = (q.num.natAbs*p.den).bits := by
    simpa only [r,ri,P,Q,BinaryRationalArithmetic.encode,BinarySignedWords.encode,value_bits] using hrm
  have hdm' : d.norm.out = v.bits := by
    simpa only [d,di,v,P,Q,BinaryRationalArithmetic.encode,value_bits] using hdm
  have hnv' : signedValue n.negative (value n.norm.out) = p.num*q.den := by
    change signedValue n.negative (value n.norm.out) =
      signedValue P.numerator.negative (value P.numerator.magnitude) *
        signedValue false (value Q.denominator) at hnv
    have hleft : signedValue P.numerator.negative (value P.numerator.magnitude) = p.num := by
      simpa only [P,BinaryRationalArithmetic.encode,BinarySignedWords.encode,value_bits] using signedValue_int p.num
    have hright : signedValue false (value Q.denominator) = (q.den:ℤ) := by
      simp only [Q,BinaryRationalArithmetic.encode,value_bits]
      rfl
    rw [hleft,hright] at hnv
    exact hnv
  have hrv' : signedValue r.negative (value r.norm.out) = q.num*p.den := by
    change signedValue r.negative (value r.norm.out) =
      signedValue Q.numerator.negative (value Q.numerator.magnitude) *
        signedValue false (value P.denominator) at hrv
    have hleft : signedValue Q.numerator.negative (value Q.numerator.magnitude) = q.num := by
      simpa only [Q,BinaryRationalArithmetic.encode,BinarySignedWords.encode,value_bits] using signedValue_int q.num
    have hright : signedValue false (value P.denominator) = (p.den:ℤ) := by
      simp only [P,BinaryRationalArithmetic.encode,value_bits]
      rfl
    rw [hleft,hright] at hrv
    exact hrv
  let r0 := BinaryRationalNormalizationMachine.initial false [] []
  let a0 := BinarySignedAdder.initial ⟨false,[]⟩ ⟨false,[]⟩
  let s0 := prepared P Q
  obtain ⟨jn,hjn,hjnr⟩ := forward_leftProduct s0 ni kn hnh
  have h1 : Runs s0 jn ⟨.rightProduct,⟨.numCollect,n,di,r0,[]⟩,ri,a0,[]⟩ := hjnr
  let s1 : State := ⟨.rightProduct,⟨.numCollect,n,di,r0,[]⟩,ri,a0,[]⟩
  obtain ⟨jr,hjr,hjrr⟩ := forward_rightProduct s1 ri kr hrh
  have h2 : Runs s1 jr ⟨.denominator,⟨.numCollect,n,di,r0,[]⟩,r,a0,[]⟩ := hjrr
  let s2 : State := ⟨.denominator,⟨.numCollect,n,di,r0,[]⟩,r,a0,[]⟩
  obtain ⟨jd,hjd,hjdr⟩ := forward_denominator s2 di kd hdh
  have h3 : Runs s2 jd ⟨.leftCollect,⟨.numCollect,n,d,r0,[]⟩,r,
      BinarySignedAdder.initial ⟨n.negative,[]⟩ ⟨r.negative,[]⟩,[]⟩ := hjdr
  have ht := load_products n d r
  obtain ⟨ka,hka,hah,hav,ham⟩ := BinarySignedAdder.run_signed_sum n.negative r.negative n.norm.out r.norm.out
  let a := BinarySignedAdder.advance ka (sumReady n r)
  have hav' : signedValue a.negative (value a.norm.out) = z := by
    change signedValue a.negative (value a.norm.out) = _ at hav
    rw [hnv',hrv'] at hav
    exact hav
  have ham' : a.norm.out = z.natAbs.bits := by
    change a.norm.out = _ at ham
    rw [hnv',hrv'] at ham
    exact ham
  let s3 : State := ⟨.add,⟨.numCollect,emptied n,d,r0,[]⟩,emptied r,sumReady n r,[]⟩
  obtain ⟨ja,hja,hjar⟩ := forward_add s3 (sumReady n r) ka hah
  have h4 : Runs s3 ja ⟨.sumCollect,⟨.numCollect,emptied n,d,r0,[]⟩,emptied r,a,[]⟩ := hjar
  have hs := transport_sum n d (emptied r) a
  have hvpos : 0 < v := Nat.mul_pos p.den_pos q.den_pos
  obtain ⟨ku,rn,rd,hku,hkur⟩ := BinaryRationalArithmeticMultiplier.normalize_outputs (summed n a) d z.natAbs v ham' hdm' hvpos
  let bi : BinaryRationalArithmeticMultiplier.State :=
    ⟨.numCollect,summed n a,d,BinaryRationalNormalizationMachine.initial a.negative [] [],[]⟩
  have hbh : (BinaryRationalArithmeticMultiplier.advance ku bi).phase = .halt := by
    rw [show BinaryRationalArithmeticMultiplier.advance ku bi = _ from hkur]
  let s4 : State := ⟨.normalize,bi,emptied r,{a with norm := {a.norm with out := []}},[]⟩
  obtain ⟨ju,hju,hjur⟩ := forward_normalize s4 bi ku hbh
  rw [show BinaryRationalArithmeticMultiplier.advance ku bi = _ from hkur] at hjur
  have hrun := ((((((prepare P Q).trans h1).trans h2).trans h3).trans ht).trans h4).trans hs
  have hall := hrun.trans hjur
  -- The scratch right product is retained, independently of the output value.
  refine ⟨(2*P.denominator.length+2*Q.denominator.length+4)+jn+jr+jd+
    (2*n.norm.out.length+2*r.norm.out.length+4)+ja+(2*a.norm.out.length+2)+ju,
    n,d,r,a,rn,rd,?_,hav',ham',?_⟩
  · let S := rationalEncodingLength p+rationalEncodingLength q+1
    have hS : 1 ≤ S := by dsimp [S]; omega
    have hS2 : S ≤ S*S := by nlinarith only [hS]
    have hS3 : S*S ≤ S^3 := by nlinarith only [Nat.mul_le_mul_left (S*S) hS]
    have hlinear : S ≤ S^3 := hS2.trans hS3
    have hnsize := nat_size_mul_le p.num.natAbs q.den
    have hrsize := nat_size_mul_le q.num.natAbs p.den
    have hdsize := nat_size_mul_le p.den q.den
    have habs := Int.natAbs_add_le (p.num*q.den) (q.num*p.den)
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at habs
    have hzsize := (Nat.size_le_size habs).trans (nat_size_add_le _ _)
    have hnS : (p.num.natAbs*q.den).size ≤ S := by
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hrS : (q.num.natAbs*p.den).size ≤ S := by
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hdS : v.size ≤ S := by
      dsimp [v,S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hzS : z.natAbs.size ≤ S+1 := by
      change z.natAbs.size ≤ max _ _ + 1 at hzsize
      have hm := max_le hnS hrS
      omega
    have hsumS : z.natAbs.size+v.size+1 ≤ 4*S := by omega
    have hcube := Nat.pow_le_pow_left hsumS 3
    have hnlen : n.norm.out.length ≤ S := by simpa only [hnm',Nat.size_eq_bits_len] using hnS
    have hrlen : r.norm.out.length ≤ S := by simpa only [hrm',Nat.size_eq_bits_len] using hrS
    have halen : a.norm.out.length ≤ S+1 := by simpa only [ham',Nat.size_eq_bits_len] using hzS
    have hmax : max n.norm.out.length r.norm.out.length ≤ S := max_le hnlen hrlen
    have haBound : ka ≤ 23*S+26 := by omega
    have hps : P.numerator.magnitude.length ≤ S := by
      dsimp [P,BinaryRationalArithmetic.encode,BinarySignedWords.encode]
      simp only [Nat.size_eq_bits_len]
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hqs : Q.numerator.magnitude.length ≤ S := by
      dsimp [Q,BinaryRationalArithmetic.encode,BinarySignedWords.encode]
      simp only [Nat.size_eq_bits_len]
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hpds : P.denominator.length ≤ S := by
      dsimp [P,BinaryRationalArithmetic.encode]
      simp only [Nat.size_eq_bits_len]
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hqds : Q.denominator.length ≤ S := by
      dsimp [Q,BinaryRationalArithmetic.encode]
      simp only [Nat.size_eq_bits_len]
      dsimp [S,rationalEncodingLength,numeratorBits,denominatorBits]; omega
    have hsum1 : P.numerator.magnitude.length+Q.denominator.length+1 ≤ 3*S := by omega
    have hsum2 : Q.numerator.magnitude.length+P.denominator.length+1 ≤ 3*S := by omega
    have hsum3 : P.denominator.length+Q.denominator.length+1 ≤ 3*S := by omega
    have hnprod := Nat.mul_le_mul hps hsum1
    have hrprod := Nat.mul_le_mul hqs hsum2
    have hdprod := Nat.mul_le_mul hpds hsum3
    have hnBound : kn ≤ 60*S*S+12*S+9 := by nlinarith only [hkn,hnprod,hsum1]
    have hrBound : kr ≤ 60*S*S+12*S+9 := by nlinarith only [hkr,hrprod,hsum2]
    have hdBound : kd ≤ 60*S*S+12*S+9 := by nlinarith only [hkd,hdprod,hsum3]
    have huBound : ku ≤ 64008*S^3+5 := by nlinarith only [hku,hcube,hsumS,hlinear]
    change _ ≤ 100000*S^3
    nlinarith only [hjn,hjr,hjd,hja,hju,hnBound,hrBound,hdBound,haBound,huBound,
      hnlen,hrlen,halen,hpds,hqds,hS3,hlinear,hS]
  · exact hall

end IdentityTesting.BinaryRationalArithmeticAdder
