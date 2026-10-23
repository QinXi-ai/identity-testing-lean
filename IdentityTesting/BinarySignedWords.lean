import IdentityTesting.BinaryRationalNormalization

namespace IdentityTesting.BinarySignedWords
open BinaryArithmetic

def signedValue (negative : Bool) (m : ℕ) : ℤ := if negative then -(m : ℤ) else m

structure Word where
  negative : Bool
  magnitude : List Bool
  deriving DecidableEq, Repr

def Word.value (w : Word) : ℤ := signedValue w.negative (BinaryArithmetic.value w.magnitude)

def encode (z : ℤ) : Word := ⟨decide (z < 0), z.natAbs.bits⟩

theorem signedValue_int (z : ℤ) : signedValue (decide (z < 0)) z.natAbs = z := by
  cases z <;> simp [signedValue] <;> omega

theorem encode_value (z : ℤ) : (encode z).value = z := by
  simpa only [Word.value, encode, value_bits] using signedValue_int z

theorem signedValue_mul (a b : Bool) (m n : ℕ) :
    signedValue (xor a b) (m * n) = signedValue a m * signedValue b n := by
  cases a <;> cases b <;> simp [signedValue]

theorem clear_zero_sign (sg : Bool) (xs : List Bool) :
    signedValue (if xs = [] then false else sg) (value xs) = signedValue sg (value xs) := by
  by_cases h : xs = []
  · cases sg <;> simp [h, signedValue, value]
  · simp [h]

end IdentityTesting.BinarySignedWords
