import IdentityTesting.RationalEncodingBounds

/-!
# Explicit binary arithmetic with primitive execution traces

The executable arithmetic below operates on little-endian `List Bool`. Natural
number addition/multiplication occur only in the denotation and in proofs, never
as arithmetic instructions of the algorithms. A trace records Boolean gates,
single-cell reads/writes, head movements, and finite-control branches. Its length
is the cost; no polynomial is assigned as the definition of an arithmetic cost.

This is an instrumented recursive bit-list semantics. It is not a theorem about
Lean's runtime, nor yet a compilation/simulation theorem for Mathlib's `TM2`.
In particular it does not certify `Rat` normalization, division, or the complete
allocation oracle. The copy routine charges for saving/restoring one bit per
recursive frame, so reuse of the multiplier input is not charged as a free copy.
-/

namespace IdentityTesting.BinaryArithmetic

/-- Each constructor is one elementary bit/control action, not an integer op. -/
inductive BitOp where
  | readCell | writeCell | moveHead | branch | xorGate | andGate | orGate
  deriving DecidableEq, Repr

/-- Instrumentation is semantic evidence, not a trace allocated by the algorithm. -/
structure Execution (α : Type) where
  value : α
  trace : List BitOp
  deriving Repr

def Execution.cost (r : Execution α) : ℕ := r.trace.length

def Execution.bind (r : Execution α) (f : α → Execution β) : Execution β :=
  let s := f r.value
  ⟨s.value, r.trace ++ s.trace⟩

@[simp] theorem Execution.bind_cost (r : Execution α) (f : α → Execution β) :
    (r.bind f).cost = r.cost + (f r.value).cost := by
  simp [Execution.bind, Execution.cost]

def xorBit (a b : Bool) : Execution Bool := ⟨xor a b, [.xorGate]⟩
def andBit (a b : Bool) : Execution Bool := ⟨a && b, [.andGate]⟩
def orBit (a b : Bool) : Execution Bool := ⟨a || b, [.orGate]⟩

/-- The usual shared-XOR five-gate full adder. -/
def fullAdder (a b c : Bool) : Execution (Bool × Bool) :=
  (xorBit a b).bind fun p =>
  (xorBit p c).bind fun s =>
  (andBit a b).bind fun g =>
  (andBit p c).bind fun h =>
  (orBit g h).bind fun carry => ⟨(s, carry), []⟩

theorem fullAdder_correct (a b c : Bool) :
    (fullAdder a b c).value.1.toNat + 2 * (fullAdder a b c).value.2.toNat =
      a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem fullAdder_cost (a b c : Bool) : (fullAdder a b c).cost = 5 := by
  rfl

/-- Denotation only; this unbounded-natural operation is not executed. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

private def inspectPair : List BitOp := [.readCell, .branch, .readCell, .branch]
private def openRound : List BitOp := [.moveHead, .moveHead, .writeCell, .moveHead]
private def closeRound : List BitOp :=
  [.readCell, .moveHead, .writeCell, .moveHead, .branch]

/-- One output cell and one move; also implements a one-bit left shift. -/
def prependBit (b : Bool) (xs : List Bool) : Execution (List Bool) :=
  ⟨b :: xs, [.writeCell, .moveHead]⟩

private def addRound (a b c : Bool) (rest : Bool → Execution (List Bool)) :
    Execution (List Bool) :=
  let f := fullAdder a b c
  let r := rest f.value.2
  ⟨f.value.1 :: r.value,
    inspectPair ++ f.trace ++ openRound ++ r.trace ++ closeRound⟩

/-- Ripple-carry addition, retaining harmless high zero bits. The recursive
frame stores only the one output bit, charged in `openRound`/`closeRound`. -/
def add : List Bool → List Bool → Bool → Execution (List Bool)
  | [], [], c =>
      if c then ⟨[true], inspectPair ++ [.writeCell, .moveHead]⟩
      else ⟨[], inspectPair⟩
  | a :: xs, [], c => addRound a false c (fun d => add xs [] d)
  | [], b :: ys, c => addRound false b c (fun d => add [] ys d)
  | a :: xs, b :: ys, c => addRound a b c (fun d => add xs ys d)

private theorem addRound_cost (a b c : Bool) (r : Bool → Execution (List Bool)) :
    (addRound a b c r).cost = (r (fullAdder a b c).value.2).cost + 18 := by
  simp [addRound, Execution.cost, inspectPair, openRound, closeRound,
    fullAdder, Execution.bind, xorBit, andBit, orBit]

theorem add_correct : ∀ (xs ys : List Bool) (c : Bool),
    value (add xs ys c).value = value xs + value ys + c.toNat
  | [], [], c => by cases c <;> simp [add, value]
  | a :: xs, [], c => by
      have ih := add_correct xs [] (fullAdder a false c).value.2
      have hf := fullAdder_correct a false c
      rw [add]
      change (fullAdder a false c).value.1.toNat +
        2 * value (add xs [] (fullAdder a false c).value.2).value =
          a.toNat + 2 * value xs + 0 + c.toNat
      rw [ih]
      simp only [value, Bool.toNat_false] at *
      omega
  | [], b :: ys, c => by
      have ih := add_correct [] ys (fullAdder false b c).value.2
      have hf := fullAdder_correct false b c
      rw [add]
      change (fullAdder false b c).value.1.toNat +
        2 * value (add [] ys (fullAdder false b c).value.2).value =
          0 + (b.toNat + 2 * value ys) + c.toNat
      rw [ih]
      simp only [value, Bool.toNat_false] at *
      omega
  | a :: xs, b :: ys, c => by
      have ih := add_correct xs ys (fullAdder a b c).value.2
      have hf := fullAdder_correct a b c
      rw [add]
      change (fullAdder a b c).value.1.toNat +
        2 * value (add xs ys (fullAdder a b c).value.2).value =
          (a.toNat + 2 * value xs) + (b.toNat + 2 * value ys) + c.toNat
      rw [ih]
      omega

theorem add_length : ∀ (xs ys : List Bool) (c : Bool),
    (add xs ys c).value.length ≤ max xs.length ys.length + 1
  | [], [], c => by cases c <;> simp [add, inspectPair]
  | a :: xs, [], c => by
      have ih := add_length xs [] (fullAdder a false c).value.2
      simpa [add, addRound] using Nat.succ_le_succ ih
  | [], b :: ys, c => by
      have ih := add_length [] ys (fullAdder false b c).value.2
      simpa [add, addRound] using Nat.succ_le_succ ih
  | a :: xs, b :: ys, c => by
      have ih := add_length xs ys (fullAdder a b c).value.2
      simp only [add, addRound, List.length_cons]
      omega

theorem add_cost : ∀ (xs ys : List Bool) (c : Bool),
    (add xs ys c).cost ≤ 18 * max xs.length ys.length + 6
  | [], [], c => by cases c <;> simp [add, Execution.cost, inspectPair]
  | a :: xs, [], c => by
      have ih := add_cost xs [] (fullAdder a false c).value.2
      rw [add, addRound_cost]
      simp only [List.length_cons, List.length_nil, Nat.max_zero] at *
      omega
  | [], b :: ys, c => by
      have ih := add_cost [] ys (fullAdder false b c).value.2
      rw [add, addRound_cost]
      simp only [List.length_cons, List.length_nil, Nat.zero_max] at *
      omega
  | a :: xs, b :: ys, c => by
      have ih := add_cost xs ys (fullAdder a b c).value.2
      rw [add, addRound_cost]
      simp only [List.length_cons] at *
      omega

theorem add_step_value (xs ys : List Bool) (c : Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    (add xs ys c).value =
      (fullAdder (xs.headD false) (ys.headD false) c).value.1 ::
        (add xs.tail ys.tail (fullAdder (xs.headD false) (ys.headD false) c).value.2).value := by
  cases xs <;> cases ys <;> simp_all [add, addRound]

private def copyOpen : List BitOp :=
  [.readCell, .branch, .moveHead, .writeCell, .moveHead]
private def copyClose : List BitOp :=
  [.readCell, .moveHead, .writeCell, .moveHead, .moveHead]

/-- Copy a bit string while preserving its source. Ten actions per bit cover
source read/advance/restore, a saved frame bit, and a destination write/move. -/
def copy : List Bool → Execution (List Bool)
  | [] => ⟨[], [.readCell, .branch]⟩
  | b :: bs =>
      let r := copy bs
      ⟨b :: r.value, copyOpen ++ r.trace ++ copyClose⟩

@[simp] theorem copy_value (xs : List Bool) : (copy xs).value = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [copy, ih]

@[simp] theorem copy_cost (xs : List Bool) : (copy xs).cost = 10 * xs.length + 2 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp [copy, Execution.cost, copyOpen, copyClose] at *
      omega

private def mulOpen : List BitOp := [.readCell, .branch, .moveHead]
private def mulClose : List BitOp := [.readCell, .moveHead, .branch]

/-- Shift-and-add multiplication. Each recursive use gets an explicitly charged
copy of the other input. No unbounded integer multiplication is executed. -/
def mul : List Bool → List Bool → Execution (List Bool)
  | [], _ => ⟨[], [.readCell, .branch]⟩
  | b :: bs, ys =>
      let ycopy := copy ys
      let r := mul bs ycopy.value
      let shifted := prependBit false r.value
      let z := if b then add ys shifted.value false else shifted
      ⟨z.value, mulOpen ++ ycopy.trace ++ r.trace ++ shifted.trace ++ mulClose ++
        (if b then (add ys shifted.value false).trace else [])⟩

theorem mul_correct (xs ys : List Bool) :
    value (mul xs ys).value = value xs * value ys := by
  induction xs with
  | nil => simp [mul, value]
  | cons b bs ih =>
      cases b with
      | false => simp [mul, prependBit, value, ih, Nat.mul_assoc]
      | true =>
          simp only [mul, copy_value, Bool.true_eq, ↓reduceIte]
          rw [add_correct]
          simp only [prependBit, value, Bool.toNat_false, Bool.toNat_true, zero_add,
            Nat.add_zero, ih]
          ring

theorem mul_length (xs ys : List Bool) :
    (mul xs ys).value.length ≤ 2 * xs.length + ys.length := by
  induction xs with
  | nil => simp [mul]
  | cons b bs ih =>
      have ha := add_length ys (false :: (mul bs ys).value) false
      cases b <;> simp only [mul, copy_value, Bool.false_eq_true, ↓reduceIte,
        Bool.true_eq, prependBit, List.length_cons] at * <;> omega

private theorem mul_cost_cons (b : Bool) (bs ys : List Bool) :
    (mul (b :: bs) ys).cost =
      (copy ys).cost + (mul bs ys).cost + 8 +
        (if b then (add ys (false :: (mul bs ys).value) false).cost else 0) := by
  cases b <;> simp [mul, Execution.cost, mulOpen, mulClose, prependBit] <;> omega

/-- A polynomial upper bound derived from the executed traces. The degree is
deliberately loose; this theorem is about this bit-list semantics only. -/
theorem mul_cost (xs ys : List Bool) :
    (mul xs ys).cost ≤ 64 * xs.length * (xs.length + ys.length + 1) + 2 := by
  induction xs with
  | nil => simp [mul, Execution.cost]
  | cons b bs ih =>
      have hl := mul_length bs ys
      have ha := add_cost ys (false :: (mul bs ys).value) false
      rw [mul_cost_cons, copy_cost]
      simp only [List.length_cons] at *
      have hm : max ys.length ((mul bs ys).value.length + 1) ≤
          2 * bs.length + ys.length + 1 := by omega
      have hcost : (add ys (false :: (mul bs ys).value) false).cost ≤
          18 * (2 * bs.length + ys.length + 1) + 6 := by omega
      cases b <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] <;>
        nlinarith

/-- The actual canonical binary input denotes the supplied natural number. -/
@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [value]
  | bit b n h ih =>
      rw [Nat.bits_append_bit _ _ h]
      simp only [value, ih, Nat.bit_val]
      omega

/-- Input-length interface: no premise asking the caller to supply a binary
representation or its size remains. `Nat.bits` is the input encoding here,
not an extra conversion whose Lean runtime is included in the trace. -/
theorem add_binary_inputs (m n : ℕ) :
    value (add m.bits n.bits false).value = m + n ∧
    (add m.bits n.bits false).cost ≤ 18 * max m.size n.size + 6 := by
  constructor
  · simpa using add_correct m.bits n.bits false
  · simpa only [Nat.size_eq_bits_len] using add_cost m.bits n.bits false

theorem mul_binary_inputs (m n : ℕ) :
    value (mul m.bits n.bits).value = m * n ∧
    (mul m.bits n.bits).cost ≤ 64 * m.size * (m.size + n.size + 1) + 2 := by
  constructor
  · simpa using mul_correct m.bits n.bits
  · simpa only [Nat.size_eq_bits_len] using mul_cost m.bits n.bits

end IdentityTesting.BinaryArithmetic
