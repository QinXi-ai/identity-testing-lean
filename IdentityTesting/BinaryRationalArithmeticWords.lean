import IdentityTesting.BinarySignedWords
import IdentityTesting.RationalEncodingBounds

/-! The bit-level rational input/output interface. Its length is exactly the
reduced rational encoding length used by the algorithm's operand bounds. -/
namespace IdentityTesting.BinaryRationalArithmetic
open BinaryArithmetic BinarySignedWords RationalComputation

structure Word where
  numerator : BinarySignedWords.Word
  denominator : List Bool
  deriving DecidableEq, Repr

def Word.value (w : Word) : ℚ := (w.numerator.value : ℚ) / BinaryArithmetic.value w.denominator

def Word.length (w : Word) : ℕ := 1 + w.numerator.magnitude.length + w.denominator.length

def encode (q : ℚ) : Word := ⟨BinarySignedWords.encode q.num, q.den.bits⟩

theorem encode_value (q : ℚ) : (encode q).value = q := by
  simp only [Word.value, encode, BinarySignedWords.encode_value, value_bits, Rat.num_div_den]

theorem encode_length (q : ℚ) : (encode q).length = rationalEncodingLength q := by
  simp only [encode, Word.length, BinarySignedWords.encode, Nat.size_eq_bits_len,
    rationalEncodingLength, numeratorBits, denominatorBits]

theorem encode_denominator_pos (q : ℚ) : 0 < value (encode q).denominator := by
  simpa [encode] using q.den_pos

theorem numerator_magnitude_bound (q : ℚ) : (encode q).numerator.magnitude.length ≤ rationalEncodingLength q := by
  simp only [encode, BinarySignedWords.encode, Nat.size_eq_bits_len,
    rationalEncodingLength, numeratorBits, denominatorBits]
  omega

theorem denominator_length_bound (q : ℚ) : (encode q).denominator.length ≤ rationalEncodingLength q := by
  simp only [encode, Nat.size_eq_bits_len, rationalEncodingLength, numeratorBits, denominatorBits]
  omega

end IdentityTesting.BinaryRationalArithmetic
