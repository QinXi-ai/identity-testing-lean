import IdentityTesting.BinaryRationalArithmeticWords
import IdentityTesting.BinarySignedNegation

namespace IdentityTesting.BinaryRationalArithmetic
open BinaryArithmetic BinarySignedWords

theorem encode_negation (q : ℚ) :
    encode (-q) = ⟨BinarySignedNegation.step (encode q).numerator,(encode q).denominator⟩ := by
  by_cases hz : q = 0
  · subst q
    norm_num [encode,BinarySignedWords.encode,BinarySignedNegation.step]
  · have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hz
    have hb : q.num.natAbs.bits ≠ [] := by
      intro h
      have hv := congrArg value h
      simp only [value_bits,value] at hv
      exact hn (Int.natAbs_eq_zero.mp hv)
    by_cases hs : q.num < 0
    · have hqneg : q < 0 := Rat.num_neg.mp hs
      simp [encode,BinarySignedWords.encode,BinarySignedNegation.step,hb,hs,hqneg.le]
    · have hp : 0 < q.num := by omega
      have hqpos : 0 < q := Rat.num_pos.mp hp
      simp [encode,BinarySignedWords.encode,BinarySignedNegation.step,hb,hs,hqpos]

end IdentityTesting.BinaryRationalArithmetic
