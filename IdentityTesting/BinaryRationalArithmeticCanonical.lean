import IdentityTesting.BinaryRationalArithmeticWords

namespace IdentityTesting.BinaryRationalArithmetic
open BinaryArithmetic BinarySignedWords

/-- Value, canonical magnitudes, and the zero-sign rule determine the entire
rational encoding. This connects arithmetic machines to reusable word callers. -/
theorem canonical_word_eq_encode (w : Word) (q : ℚ)
    (hv : w.value = q)
    (hn : w.numerator.magnitude = q.num.natAbs.bits)
    (hd : w.denominator = q.den.bits)
    (hz : w.numerator.magnitude = [] → w.numerator.negative = false) :
    w = encode q := by
  have hd0 : (q.den:ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt q.den_pos)
  have he : ((signedValue w.numerator.negative q.num.natAbs : ℤ):ℚ) / q.den = (q.num:ℚ) / q.den := by
    simpa only [Word.value,BinarySignedWords.Word.value,hn,hd,value_bits,Rat.num_div_den] using hv
  have hnum : signedValue w.numerator.negative q.num.natAbs = q.num := by
    have hc := (div_left_inj' hd0).mp he
    exact_mod_cast hc
  have hs : w.numerator.negative = decide (q.num < 0) := by
    cases hsg : w.numerator.negative with
    | false =>
        simp only [hsg] at hnum
        change (q.num.natAbs:ℤ) = q.num at hnum
        have hnonneg : 0 ≤ q.num := by omega
        simp [not_lt.mpr hnonneg]
    | true =>
        simp only [hsg] at hnum
        change -(q.num.natAbs:ℤ) = q.num at hnum
        have hne : q.num ≠ 0 := by
          intro hzero
          have hm : w.numerator.magnitude = [] := by simp [hn,hzero]
          have hf := hz hm
          simp [hsg] at hf
        have hneg : q.num < 0 := by omega
        simp [hneg]
  cases w with
  | mk num den =>
      cases num with
      | mk neg mag =>
          simp only [encode,BinarySignedWords.encode,Word.mk.injEq,BinarySignedWords.Word.mk.injEq]
          exact ⟨⟨hs,hn⟩,hd⟩

theorem encoded_nonpositive (q : ℚ) :
    ((encode q).numerator.negative = true ∨ (encode q).numerator.magnitude = []) ↔ q ≤ 0 := by
  have hz : q.num.natAbs.bits = [] ↔ q.num = 0 := by
    constructor
    · intro h
      have hv := congrArg value h
      simp only [value_bits,value] at hv
      exact Int.natAbs_eq_zero.mp hv
    · intro h
      simp [h]
  simp only [encode,BinarySignedWords.encode,decide_eq_true_eq,hz]
  rw [← le_iff_lt_or_eq,Rat.num_nonpos]

end IdentityTesting.BinaryRationalArithmetic
