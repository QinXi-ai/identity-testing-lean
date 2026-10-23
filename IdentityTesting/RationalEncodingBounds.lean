import IdentityTesting.RationalAllocationOracleInputs
import Mathlib.Data.Rat.Lemmas

/-! Actual reduced rational encoding sizes. These are length bounds, not a
bit-operation cost model or a claim about integer-arithmetic running time. -/
open scoped BigOperators
namespace IdentityTesting.RationalComputation

def numeratorBits (q : ℚ) : ℕ := q.num.natAbs.size
def denominatorBits (q : ℚ) : ℕ := q.den.size
def rationalEncodingLength (q : ℚ) : ℕ := 1 + numeratorBits q + denominatorBits q
def rationalVectorEncodingLength {k : ℕ} (a : Fin k → ℚ) : ℕ :=
  k + ∑ i, rationalEncodingLength (a i)

theorem rational_fraction_reduction_bounds (z : ℤ) (d : ℕ) (hd : 0 < d) :
    (((z : ℚ) / d).num).natAbs ≤ z.natAbs ∧ ((z : ℚ) / d).den ≤ d := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  obtain ⟨c, hn, hden⟩ := Rat.num_den_mk hdZ
    (show (z : ℚ) / d = Rat.divInt z (d : ℤ) by
      simp only [Rat.divInt_eq_div, Int.cast_natCast])
  have hc : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hden
    exact hdZ hden
  have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hn' := congrArg Int.natAbs hn
  have hd' := congrArg Int.natAbs hden
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn' hd'
  exact ⟨(Nat.le_mul_of_pos_left _ hcpos).trans_eq hn'.symm,
    (Nat.le_mul_of_pos_left _ hcpos).trans_eq hd'.symm⟩

theorem rational_mul_components (p q : ℚ) :
    (p * q).num.natAbs ≤ p.num.natAbs * q.num.natAbs ∧
      (p * q).den ≤ p.den * q.den := by
  have hrep : p * q = ((p.num * q.num : ℤ) : ℚ) / (p.den * q.den : ℕ) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  rw [hrep]
  simpa only [Int.natAbs_mul] using
    rational_fraction_reduction_bounds (p.num * q.num) (p.den * q.den) (Nat.mul_pos p.den_pos q.den_pos)

theorem rational_add_components (p q : ℚ) :
    (p + q).num.natAbs ≤ p.num.natAbs * q.den + q.num.natAbs * p.den ∧
      (p + q).den ≤ p.den * q.den := by
  have hrep : p + q = ((p.num * q.den + q.num * p.den : ℤ) : ℚ) / (p.den * q.den : ℕ) := by
    rw [Rat.add_num_den, Rat.divInt_eq_div]
    push_cast
    ring
  have h := rational_fraction_reduction_bounds (p.num * q.den + q.num * p.den)
    (p.den * q.den) (Nat.mul_pos p.den_pos q.den_pos)
  rw [← hrep] at h
  have habs := Int.natAbs_add_le (p.num * q.den) (q.num * p.den)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at habs
  exact ⟨h.1.trans habs, h.2⟩

theorem nat_size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.lt_size_self m).le (Nat.lt_size_self n) (by positivity)

theorem nat_size_add_le (m n : ℕ) : (m + n).size ≤ max m.size n.size + 1 := by
  apply Nat.size_le.mpr
  have hm := (Nat.lt_size_self m).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left m.size n.size))
  have hn := (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right m.size n.size))
  rw [pow_succ]
  omega

theorem rational_mul_bits (p q : ℚ) :
    numeratorBits (p * q) ≤ numeratorBits p + numeratorBits q ∧
      denominatorBits (p * q) ≤ denominatorBits p + denominatorBits q := by
  have h := rational_mul_components p q
  exact ⟨(Nat.size_le_size h.1).trans (nat_size_mul_le _ _),
    (Nat.size_le_size h.2).trans (nat_size_mul_le _ _)⟩

theorem rational_add_bits (p q : ℚ) :
    numeratorBits (p + q) ≤ max (numeratorBits p + denominatorBits q)
      (numeratorBits q + denominatorBits p) + 1 ∧
      denominatorBits (p + q) ≤ denominatorBits p + denominatorBits q := by
  have h := rational_add_components p q
  constructor
  · apply (Nat.size_le_size h.1).trans
    apply (nat_size_add_le _ _).trans
    exact Nat.add_le_add_right (max_le_max (nat_size_mul_le _ _) (nat_size_mul_le _ _)) 1
  · exact (Nat.size_le_size h.2).trans (nat_size_mul_le _ _)

theorem rational_neg_bits (q : ℚ) :
    numeratorBits (-q) = numeratorBits q ∧ denominatorBits (-q) = denominatorBits q := by
  simp [numeratorBits, denominatorBits]

theorem rational_inv_bits (q : ℚ) (hq : q ≠ 0) :
    numeratorBits q⁻¹ = denominatorBits q ∧ denominatorBits q⁻¹ = numeratorBits q := by
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  simp only [numeratorBits, denominatorBits, Rat.num_inv, Int.natAbs_mul,
    Int.natAbs_sign_of_ne_zero hn, Int.natAbs_natCast, one_mul, Rat.den_inv_of_ne_zero hq,
    and_self]

theorem rational_mul_encoding (p q : ℚ) :
    rationalEncodingLength (p * q) ≤ rationalEncodingLength p + rationalEncodingLength q := by
  obtain ⟨hn, hd⟩ := rational_mul_bits p q
  unfold rationalEncodingLength
  omega

theorem rational_add_encoding (p q : ℚ) :
    rationalEncodingLength (p + q) ≤ 2 * (rationalEncodingLength p + rationalEncodingLength q) + 1 := by
  obtain ⟨hn, hd⟩ := rational_add_bits p q
  unfold rationalEncodingLength
  omega

theorem rational_neg_encoding (q : ℚ) : rationalEncodingLength (-q) = rationalEncodingLength q := by
  obtain ⟨hn, hd⟩ := rational_neg_bits q
  simp only [rationalEncodingLength, hn, hd]

theorem rational_sub_encoding (p q : ℚ) :
    rationalEncodingLength (p - q) ≤ 2 * (rationalEncodingLength p + rationalEncodingLength q) + 1 := by
  simpa only [sub_eq_add_neg, rational_neg_encoding] using rational_add_encoding p (-q)

theorem rational_inv_encoding (q : ℚ) (hq : q ≠ 0) :
    rationalEncodingLength q⁻¹ = rationalEncodingLength q := by
  obtain ⟨hn, hd⟩ := rational_inv_bits q hq
  simp only [rationalEncodingLength, hn, hd]
  omega

theorem rational_div_encoding (p q : ℚ) (hq : q ≠ 0) :
    rationalEncodingLength (p / q) ≤ rationalEncodingLength p + rationalEncodingLength q := by
  simpa only [div_eq_mul_inv, rational_inv_encoding q hq] using rational_mul_encoding p q⁻¹

/-- Also covers Lean's total division operation at a zero denominator. -/
theorem rational_div_encoding_le (p q : ℚ) :
    rationalEncodingLength (p / q) ≤ rationalEncodingLength p + rationalEncodingLength q := by
  by_cases hq : q = 0
  · subst q
    norm_num [rationalEncodingLength, numeratorBits, denominatorBits]
  · exact rational_div_encoding p q hq

theorem rational_pow_bits (q : ℚ) (n : ℕ) :
    numeratorBits (q ^ n) ≤ n * numeratorBits q + 1 ∧
      denominatorBits (q ^ n) ≤ n * denominatorBits q + 1 := by
  induction n with
  | zero => norm_num [numeratorBits, denominatorBits]
  | succ n ih =>
    rw [pow_succ]
    obtain ⟨hn, hd⟩ := rational_mul_bits (q ^ n) q
    constructor <;> simp only [Nat.succ_mul] <;> omega

theorem rational_pow_encoding (q : ℚ) (n : ℕ) :
    rationalEncodingLength (q ^ n) ≤ n * rationalEncodingLength q + 3 := by
  obtain ⟨hn, hd⟩ := rational_pow_bits q n
  unfold rationalEncodingLength
  nlinarith

theorem rational_lt_pow_numeratorBits (q : ℚ) : q < 2 ^ numeratorBits q := by
  have hn : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
    rw [Int.cast_natAbs, Int.cast_le]
    exact le_abs_self q.num
  have hd0 : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hd1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hsize : (q.num.natAbs : ℚ) < 2 ^ numeratorBits q := by
    exact_mod_cast Nat.lt_size_self q.num.natAbs
  calc
    q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
    _ ≤ (q.num.natAbs : ℚ) / q.den := div_le_div_of_nonneg_right hn hd0.le
    _ ≤ (q.num.natAbs : ℚ) := div_le_self (by positivity) hd1
    _ < _ := hsize

theorem rational_positive_magnitude (q : ℚ) (hq : 0 < q) :
    q ≤ 2 ^ rationalEncodingLength q ∧ 1 / q ≤ 2 ^ rationalEncodingLength q := by
  have hn : numeratorBits q ≤ rationalEncodingLength q := by unfold rationalEncodingLength; omega
  have hd : denominatorBits q ≤ rationalEncodingLength q := by unfold rationalEncodingLength; omega
  constructor
  · exact (rational_lt_pow_numeratorBits q).le.trans (pow_le_pow_right₀ (by norm_num) hn)
  · have h := (rational_lt_pow_numeratorBits q⁻¹).le
    rw [(rational_inv_bits q (ne_of_gt hq)).1] at h
    simpa only [one_div] using h.trans (pow_le_pow_right₀ (by norm_num) hd)

theorem oracleDyadicPrecision_encoding_le (C δ : ℚ) (hδ : 0 < δ) :
    oracleDyadicPrecision C δ ≤ rationalEncodingLength C + rationalEncodingLength δ + 1 := by
  have hp := oracleDyadicPrecision_le C δ (numeratorBits (C / δ))
    (rational_lt_pow_numeratorBits (C / δ)).le
  have he := rational_div_encoding C δ (ne_of_gt hδ)
  have hn : numeratorBits (C / δ) ≤ rationalEncodingLength (C / δ) := by
    unfold rationalEncodingLength
    omega
  omega

theorem rational_sum_bits {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    numeratorBits (∑ i ∈ s, f i) ≤ (∑ i ∈ s, rationalEncodingLength (f i)) + 1 ∧
      denominatorBits (∑ i ∈ s, f i) ≤ (∑ i ∈ s, denominatorBits (f i)) + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num [numeratorBits, denominatorBits]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    obtain ⟨hn, hd⟩ := rational_add_bits (f a) (∑ i ∈ s, f i)
    have hds : (∑ i ∈ s, denominatorBits (f i)) ≤ ∑ i ∈ s, rationalEncodingLength (f i) := by
      apply Finset.sum_le_sum
      intro i _
      unfold rationalEncodingLength
      omega
    unfold rationalEncodingLength at *
    constructor <;> omega

theorem rational_sum_encoding {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    rationalEncodingLength (∑ i ∈ s, f i) ≤ 2 * (∑ i ∈ s, rationalEncodingLength (f i)) + 3 := by
  obtain ⟨hn, hd⟩ := rational_sum_bits s f
  have hds : (∑ i ∈ s, denominatorBits (f i)) ≤ ∑ i ∈ s, rationalEncodingLength (f i) := by
    apply Finset.sum_le_sum
    intro i _
    unfold rationalEncodingLength
    omega
  change 1 + numeratorBits (∑ i ∈ s, f i) + denominatorBits (∑ i ∈ s, f i) ≤
    2 * (∑ i ∈ s, rationalEncodingLength (f i)) + 3
  omega

theorem rational_vector_sum_encoding {k : ℕ} (a : Fin k → ℚ) :
    rationalEncodingLength (∑ i, a i) ≤ 2 * rationalVectorEncodingLength a + 3 := by
  have h := rational_sum_encoding Finset.univ a
  unfold rationalVectorEncodingLength
  omega

end IdentityTesting.RationalComputation
