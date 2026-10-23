import IdentityTesting.BinarySubtraction
import IdentityTesting.BinaryWordNormalization

/-! Functional binary long division. This module proves the exact quotient and
remainder, including canonical output lengths. Machine execution/cost is a
separate next interface, not inferred merely from this executable definition. -/
namespace IdentityTesting.BinaryLongDivision
open BinaryArithmetic BinarySubtraction BinaryWordNormalization

def digit (b : Bool) (d q r : List Bool) : List Bool × List Bool :=
  let trial := b :: r
  let diff := subtract trial d false
  if diff.2 then (false :: q, trial) else (true :: q, diff.1)

theorem digit_correct (b : Bool) (d q r : List Bool) (hr : value r < value d) :
    value (digit b d q r).1 * value d + value (digit b d q r).2 =
      2 * (value q * value d + value r) + b.toNat ∧
    value (digit b d q r).2 < value d := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  by_cases he : (subtract (b :: r) d false).2 = true
  · have ht := (subtract_borrow (b :: r) d).mp he
    simp only [digit, he, ↓reduceIte]
    constructor
    · simp only [value, Bool.toNat_false]
      ring
    · exact ht
  · have hf : (subtract (b :: r) d false).2 = false := by
      cases hc : (subtract (b :: r) d false).2 <;> simp_all
    have hc := subtract_correct (b :: r) d false
    simp only [hf, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, value] at hc
    simp only [digit, hf, Bool.false_eq_true, ↓reduceIte]
    constructor
    · simp only [value, Bool.toNat_true]
      nlinarith
    · nlinarith

theorem digit_lengths (b : Bool) (d q r : List Bool) :
    (digit b d q r).1.length = q.length + 1 ∧
      (digit b d q r).2.length ≤ max (r.length + 1) d.length := by
  dsimp only [digit]
  split
  · simp only [List.length_cons]
    exact ⟨True.intro, le_max_left _ _⟩
  · simp [subtract_length]

def loop : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [], _, q, r => (q, r)
  | b :: bs, d, q, r =>
      let s := digit b d q r
      loop bs d s.1 s.2

def msbValue : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat * 2 ^ bs.length + msbValue bs

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih => simp only [List.cons_append, value, ih, List.length_cons, pow_succ]; ring

theorem msbValue_eq (xs : List Bool) : msbValue xs = value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, value_append]
      simp only [msbValue, List.length_reverse, value, List.length_nil, Nat.mul_zero,
        Nat.add_zero, ih]
      ring

theorem loop_correct (bits d q r : List Bool) (hr : value r < value d) :
    value (loop bits d q r).1 * value d + value (loop bits d q r).2 =
      (value q * value d + value r) * 2 ^ bits.length + msbValue bits ∧
    value (loop bits d q r).2 < value d := by
  induction bits generalizing q r with
  | nil =>
      constructor
      · simp [loop, msbValue]
      · exact hr
  | cons b bs ih =>
      have hd := digit_correct b d q r hr
      have hi := ih (digit b d q r).1 (digit b d q r).2 hd.2
      constructor
      · simp only [loop]
        rw [hi.1]
        have he := congrArg (fun z : ℕ => z * 2 ^ bs.length) hd.1
        simp only [List.length_cons, pow_succ, msbValue]
        nlinarith
      · exact hi.2

theorem loop_lengths (bits d q r : List Bool) :
    (loop bits d q r).1.length = q.length + bits.length ∧
      (loop bits d q r).2.length ≤ max r.length d.length + bits.length := by
  induction bits generalizing q r with
  | nil => simp [loop]
  | cons b bs ih =>
      have hd := digit_lengths b d q r
      have hi := ih (digit b d q r).1 (digit b d q r).2
      simp only [loop, List.length_cons]
      constructor
      · omega
      · omega

def divide (xs d : List Bool) : List Bool × List Bool :=
  let raw := loop xs.reverse d [] []
  (trim raw.1, trim raw.2)

theorem divide_spec (xs d : List Bool) (hd : 0 < value d) :
    value (divide xs d).1 * value d + value (divide xs d).2 = value xs ∧
      value (divide xs d).2 < value d := by
  have h := loop_correct xs.reverse d [] [] hd
  simpa [divide, msbValue_eq, value] using h

theorem divide_quotient_remainder (xs d : List Bool) (hd : 0 < value d) :
    value (divide xs d).1 = value xs / value d ∧
      value (divide xs d).2 = value xs % value d := by
  obtain ⟨he, hr⟩ := divide_spec xs d hd
  have h := (Nat.div_mod_unique hd).mpr
    (show value (divide xs d).2 + value d * value (divide xs d).1 = value xs ∧
      value (divide xs d).2 < value d from ⟨by nlinarith [he], hr⟩)
  exact ⟨h.1.symm, h.2.symm⟩

theorem divide_canonical_lengths (xs d : List Bool) (hd : 0 < value d) :
    (divide xs d).1.length = (value xs / value d).size ∧
      (divide xs d).2.length = (value xs % value d).size := by
  have h := divide_quotient_remainder xs d hd
  unfold divide at *
  simp only [trim_length, trim_value] at *
  rw [h.1, h.2]
  exact ⟨rfl, rfl⟩

theorem divide_binary_inputs (m n : ℕ) (hn : 0 < n) :
    value (divide m.bits n.bits).1 = m / n ∧
      value (divide m.bits n.bits).2 = m % n := by
  simpa using divide_quotient_remainder m.bits n.bits (by simpa using hn)

end IdentityTesting.BinaryLongDivision
