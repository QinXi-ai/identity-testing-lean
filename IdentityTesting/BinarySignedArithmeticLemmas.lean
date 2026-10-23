import IdentityTesting.BinarySignedWords

namespace IdentityTesting.BinarySignedWords

theorem signedValue_add_same (a : Bool) (m n : ℕ) :
    signedValue a (m + n) = signedValue a m + signedValue a n := by
  cases a <;> simp [signedValue] <;> ring

theorem signedValue_sub_ordered (a b : Bool) (m n : ℕ) (hab : a ≠ b) (hnm : n ≤ m) :
    signedValue a (m - n) = signedValue a m + signedValue b n := by
  cases a <;> cases b <;> simp_all [signedValue] <;> omega

theorem signedValue_add_cases (a b : Bool) (m n : ℕ) :
    (if a = b then signedValue a (m+n) else
      if m < n then signedValue b (n-m) else signedValue a (m-n)) =
      signedValue a m + signedValue b n := by
  split
  · rename_i h
    subst b
    exact signedValue_add_same a m n
  · rename_i h
    split
    · rename_i hmn
      rw [signedValue_sub_ordered b a n m (Ne.symm h) (by omega), add_comm]
    · rename_i hmn
      exact signedValue_sub_ordered a b m n h (by omega)

end IdentityTesting.BinarySignedWords
