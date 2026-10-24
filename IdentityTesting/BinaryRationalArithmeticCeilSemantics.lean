import IdentityTesting.BinaryRationalArithmeticWords
import IdentityTesting.RationalSqrtInterval

namespace IdentityTesting.BinaryRationalArithmetic

/-- Semantic specification of integer ceiling from quotient and remainder.
The executable construction must compute both quantities with the division
machine before testing the canonical remainder's end marker. -/
theorem nat_ceil_fraction (m d : ℕ) (hd : 0 < d) :
    Nat.ceil ((m:ℚ)/d) = m/d + if m%d=0 then 0 else 1 := by
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  have hmod := Nat.mod_add_div m d
  by_cases hz : m%d=0
  · have he : m=(m/d)*d := by nlinarith only [hmod,hz]
    have hf : (m:ℚ)/(d:ℚ) = (m/d:ℕ) := by
      apply (div_eq_iff (ne_of_gt hdq)).2
      exact_mod_cast he
    rw [hf]
    simp [hz]
  · rw [if_neg hz]
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero (m/d))).2
    have hrem : m%d < d := Nat.mod_lt m hd
    have hl : (m/d)*d < m := by nlinarith only [hmod,show 0<m%d from Nat.pos_of_ne_zero hz]
    have hu : m ≤ (m/d+1)*d := by nlinarith only [hmod,hrem]
    constructor
    · apply (lt_div_iff₀ hdq).2
      exact_mod_cast hl
    · apply (div_le_iff₀ hdq).2
      exact_mod_cast hu

theorem nat_ceil_positive_rational (q : ℚ) (hq : 0 < q) :
    Nat.ceil q = q.num.natAbs/q.den + if q.num.natAbs%q.den=0 then 0 else 1 := by
  have hn : (q.num.natAbs:ℤ)=q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq.le)
  have hc : (q.num.natAbs:ℚ)=(q.num:ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
  have hf : (q.num.natAbs:ℚ)/(q.den:ℚ)=q := by rw [hc,Rat.num_div_den]
  simpa only [hf] using nat_ceil_fraction q.num.natAbs q.den q.den_pos

end IdentityTesting.BinaryRationalArithmetic
