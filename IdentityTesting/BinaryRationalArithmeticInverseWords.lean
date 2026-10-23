import IdentityTesting.BinaryRationalArithmeticWords

namespace IdentityTesting.BinaryRationalArithmetic

/-- A nonzero reciprocal reuses the sign and exchanges the two magnitude
stack roles. This is an input-layout identity, not a free runtime word copy. -/
theorem inverse_encoding (q : ℚ) (hq : q ≠ 0) :
    encode q⁻¹ = ⟨⟨(encode q).numerator.negative,(encode q).denominator⟩,(encode q).numerator.magnitude⟩ := by
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hd : (0:ℤ) < q.den := by exact_mod_cast q.den_pos
  by_cases hneg : q.num < 0
  · simp [encode,BinarySignedWords.encode,Rat.num_inv,Rat.den_inv_of_ne_zero hq,
      Int.sign_eq_neg_one_of_neg hneg,hneg,q.den_pos]
  · have hpos : 0 < q.num := by omega
    simp [encode,BinarySignedWords.encode,Rat.num_inv,Rat.den_inv_of_ne_zero hq,
      Int.sign_eq_one_of_pos hpos,hneg,q.den_pos]

end IdentityTesting.BinaryRationalArithmetic
