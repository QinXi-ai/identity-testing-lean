import IdentityTesting.BinaryRationalArithmeticCeilSizeAssembly

namespace IdentityTesting.BinaryRationalArithmeticCeilSize
open BinaryArithmetic RationalComputation

theorem encode_nat (n : ℕ) : BinaryRationalArithmetic.encode (n:ℚ) = ⟨⟨false,n.bits⟩,[true]⟩ := by
  simp [BinaryRationalArithmetic.encode,BinarySignedWords.encode]

theorem binary_rational_ceilSize_machine (q : ℚ) :
    ∃ steps, let s := initial (BinaryRationalArithmetic.encode q)
      (advance steps s).phase = .halt ∧
      output (advance steps s) = BinaryRationalArithmetic.encode ((Nat.ceil q).size:ℚ) ∧
      bitSteps steps s ≤ 8000*(rationalEncodingLength q+1)^2 := by
  by_cases hq : q<0
  · have hn : q.num<0 := Rat.num_neg.mpr hq
    have hz : Nat.ceil q=0 := Nat.ceil_eq_zero.mpr hq.le
    refine ⟨2,?_,?_,?_⟩
    · simp [advance,step,initial,BinaryRationalArithmetic.encode,BinarySignedWords.encode,hn]
    · simp [advance,step,initial,output,BinaryRationalArithmetic.encode,BinarySignedWords.encode,
        BinaryRationalArithmeticBitLength.initial,BinaryRationalArithmeticBitLength.output,hz,hn]
    · have hc : bitSteps 2 (initial (BinaryRationalArithmetic.encode q))=4 := by
        simp [bitSteps,transitionTrace,step,initial,BinaryRationalArithmetic.encode,BinarySignedWords.encode,hn]
      rw [hc]
      have hp : 0<(rationalEncodingLength q+1)^2 := by positivity
      omega
  · have hqn : 0≤q := le_of_not_gt hq
    have hn : 0≤q.num := Rat.num_nonneg.mpr hqn
    have he : BinaryRationalArithmetic.encode q = ⟨⟨false,q.num.natAbs.bits⟩,q.den.bits⟩ := by
      simp [BinaryRationalArithmetic.encode,BinarySignedWords.encode,not_lt.mpr hn]
    have hc : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg hn
    have hc' : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hc
    have hfrac : (q.num.natAbs:ℚ)/(q.den:ℚ)=q := by rw [hc',Rat.num_div_den]
    obtain ⟨k,hh,ho,hk⟩ := natural_fraction_run q.num.natAbs q.den q.den_pos
    refine ⟨k,?_,?_,?_⟩
    · rw [he]; exact hh
    · rw [he,ho,hfrac,encode_nat]
    · rw [he]
      have hb := bitSteps_le k (initial ⟨⟨false,q.num.natAbs.bits⟩,q.den.bits⟩)
      have hl : q.num.natAbs.size+q.den.size+1 ≤ rationalEncodingLength q+1 := by
        simp [rationalEncodingLength,numeratorBits,denominatorBits]
      have hp := Nat.pow_le_pow_left hl 2
      nlinarith only [hb,hk,hp]

end IdentityTesting.BinaryRationalArithmeticCeilSize
