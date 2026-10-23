import IdentityTesting.BinaryAdderMachine

/-! Exact borrow subtraction on raw binary words, the arithmetic interface for
the subsequent fixed-stack comparator/subtractor and long-division machine. -/
namespace IdentityTesting.BinarySubtraction
open BinaryArithmetic

def fullSubtractor (a b c : Bool) : Bool × Bool :=
  (xor (xor a b) c, ((!a) && b) || ((!(xor a b)) && c))

theorem fullSubtractor_correct (a b c : Bool) :
    (fullSubtractor a b c).1.toNat + b.toNat + c.toNat =
      a.toNat + 2 * (fullSubtractor a b c).2.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def subtract : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | a :: xs, [], c =>
      let f := fullSubtractor a false c
      let r := subtract xs [] f.2
      (f.1 :: r.1, r.2)
  | [], b :: ys, c =>
      let f := fullSubtractor false b c
      let r := subtract [] ys f.2
      (f.1 :: r.1, r.2)
  | a :: xs, b :: ys, c =>
      let f := fullSubtractor a b c
      let r := subtract xs ys f.2
      (f.1 :: r.1, r.2)

theorem subtract_length : ∀ (xs ys : List Bool) (c : Bool),
    (subtract xs ys c).1.length = max xs.length ys.length
  | [], [], c => by simp [subtract]
  | a :: xs, [], c => by
      rw [subtract]
      simpa using congrArg Nat.succ (subtract_length xs [] (fullSubtractor a false c).2)
  | [], b :: ys, c => by
      rw [subtract]
      simpa using congrArg Nat.succ (subtract_length [] ys (fullSubtractor false b c).2)
  | a :: xs, b :: ys, c => by
      have ih := subtract_length xs ys (fullSubtractor a b c).2
      simp only [subtract, List.length_cons]
      omega

theorem subtract_correct : ∀ (xs ys : List Bool) (c : Bool),
    value (subtract xs ys c).1 + value ys + c.toNat =
      value xs + 2 ^ max xs.length ys.length * (subtract xs ys c).2.toNat
  | [], [], c => by simp [subtract, value]
  | a :: xs, [], c => by
      have ih := subtract_correct xs [] (fullSubtractor a false c).2
      have hf := fullSubtractor_correct a false c
      simp only [List.length_nil, Nat.max_zero, value, Bool.toNat_false] at ih hf
      simp only [subtract, value, List.length_cons, List.length_nil, Nat.max_zero, pow_succ]
      nlinarith
  | [], b :: ys, c => by
      have ih := subtract_correct [] ys (fullSubtractor false b c).2
      have hf := fullSubtractor_correct false b c
      simp only [List.length_nil, Nat.zero_max, value, Bool.toNat_false] at ih hf
      simp only [subtract, value, List.length_cons, List.length_nil, Nat.zero_max, pow_succ]
      nlinarith
  | a :: xs, b :: ys, c => by
      have ih := subtract_correct xs ys (fullSubtractor a b c).2
      have hf := fullSubtractor_correct a b c
      have hm : max (xs.length + 1) (ys.length + 1) = max xs.length ys.length + 1 := by omega
      simp only [subtract, value, List.length_cons, hm, pow_succ]
      nlinarith

theorem value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih =>
      cases b <;> simp [value, pow_succ] <;> omega

theorem subtract_borrow (xs ys : List Bool) :
    (subtract xs ys false).2 = true ↔ value xs < value ys := by
  have hc := subtract_correct xs ys false
  have hv := value_lt_two_pow_length (subtract xs ys false).1
  rw [subtract_length] at hv
  simp only [Bool.toNat_false, Nat.add_zero] at hc
  cases hb : (subtract xs ys false).2 <;> simp [hb] at hc ⊢ <;> omega

theorem subtract_of_le (xs ys : List Bool) (h : value ys ≤ value xs) :
    (subtract xs ys false).2 = false ∧
      value (subtract xs ys false).1 = value xs - value ys := by
  have hb : (subtract xs ys false).2 = false := by
    cases he : (subtract xs ys false).2 with
    | false => rfl
    | true => have hh := (subtract_borrow xs ys).mp he; omega
  have hc := subtract_correct xs ys false
  simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hc
  exact ⟨hb, by omega⟩

theorem subtract_step (xs ys : List Bool) (c : Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    subtract xs ys c =
      let f := fullSubtractor (xs.headD false) (ys.headD false) c
      let r := subtract xs.tail ys.tail f.2
      (f.1 :: r.1, r.2) := by
  cases xs <;> cases ys <;> simp_all [subtract]

end IdentityTesting.BinarySubtraction
