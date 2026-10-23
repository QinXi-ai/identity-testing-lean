import IdentityTesting.BinarySubtraction

/-! A four-stack borrow subtraction/comparison machine, with the same explicit
finite controller as the adder and two additional XOR-with-true gates. -/
namespace IdentityTesting.BinarySubtractorMachine
open BinaryArithmetic BinarySubtraction

abbrev State := BinaryAdderMachine.State
abbrev Registers := BinaryAdderMachine.Registers
abbrev loopState := BinaryAdderMachine.loopState
abbrev reverseState := BinaryAdderMachine.reverseState
abbrev haltState := BinaryAdderMachine.haltState

def step (s : State) : State :=
  match s.phase with
  | .andG => { s with phase := .andH, regs := { s.regs with g := (xor s.regs.a true) && s.regs.b } }
  | .andH => { s with phase := .orC, regs := { s.regs with h := (xor s.regs.p true) && s.regs.carry } }
  | .carry => { s with phase := .reverse }
  | _ => BinaryAdderMachine.step s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def nextRegs (r : Registers) (a b : Bool) : Registers :=
  ⟨((xor a true) && b) || ((xor (xor a b) true) && r.carry), a, b, xor a b,
    xor (xor a b) r.carry, (xor a true) && b, (xor (xor a b) true) && r.carry⟩

@[simp] theorem nextRegs_sum (r : Registers) (a b : Bool) :
    (nextRegs r a b).sum = (fullSubtractor a b r.carry).1 := rfl
@[simp] theorem nextRegs_carry (r : Registers) (a b : Bool) :
    (nextRegs r a b).carry = (fullSubtractor a b r.carry).2 := by
  cases a <;> cases b <;> rfl

theorem round_steps (xs ys : List Bool) (r : Registers) (acc : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    advance 9 (loopState xs ys r acc) =
      loopState xs.tail ys.tail (nextRegs r (xs.headD false) (ys.headD false))
        ((fullSubtractor (xs.headD false) (ys.headD false) r.carry).1 :: acc) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons b ys => rfl
  | cons a xs => cases ys <;> rfl

theorem reverse_steps (r : Registers) (work out : List Bool) :
    advance (work.length + 1) (reverseState r work out) =
      haltState r (work.reverse ++ out) := by
  induction work generalizing out with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) (reverseState r (b :: bs) out) = _
      rw [advance]
      change advance (bs.length + 1) (reverseState r bs (b :: out)) = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem finish_steps (r : Registers) (acc : List Bool) :
    advance (acc.length + 3) (loopState [] [] r acc) = haltState r acc.reverse := by
  have hn : acc.length + 3 = 2 + (acc.length + 1) := by omega
  rw [hn, advance_add]
  have h : advance 2 (loopState [] [] r acc) = reverseState r acc [] := rfl
  rw [h, reverse_steps]
  simp

theorem run_subtract (xs ys : List Bool) (r : Registers) (acc : List Bool) :
    ∃ n r', n ≤ 10 * max xs.length ys.length + acc.length + 3 ∧
      advance n (loopState xs ys r acc) =
        haltState r' (acc.reverse ++ (subtract xs ys r.carry).1) ∧
      r'.carry = (subtract xs ys r.carry).2 := by
  by_cases he : xs = [] ∧ ys = []
  · rcases he with ⟨rfl, rfl⟩
    refine ⟨acc.length + 3, r, by simp, ?_, ?_⟩
    · simpa [subtract] using finish_steps r acc
    · simp [subtract]
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    let f := fullSubtractor (xs.headD false) (ys.headD false) r.carry
    let rnext := nextRegs r (xs.headD false) (ys.headD false)
    obtain ⟨n, r', hn, heq, hb⟩ := run_subtract xs.tail ys.tail rnext (f.1 :: acc)
    have hlen : max xs.length ys.length = max xs.tail.length ys.tail.length + 1 := by
      cases xs <;> cases ys <;> simp_all
    refine ⟨9 + n, r', ?_, ?_, ?_⟩
    · simp only [List.length_cons] at hn
      omega
    · rw [advance_add, round_steps xs ys r acc hne]
      change advance n (loopState xs.tail ys.tail rnext (f.1 :: acc)) = _
      rw [heq, subtract_step xs ys r.carry hne]
      simp [rnext, f, List.reverse_cons, List.append_assoc]
    · rw [subtract_step xs ys r.carry hne]
      simpa [rnext, f] using hb
termination_by xs.length + ys.length
decreasing_by
  cases xs <;> cases ys <;> simp_all <;> omega

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .andG | .andH => [.xorGate, .andGate]
  | .carry => [.branch]
  | _ => BinaryAdderMachine.transitionTrace s

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 5 := by
  have ha := BinaryAdderMachine.transition_length s
  cases hp : s.phase <;> simp_all [transitionTrace]

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 5 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

/-- Simultaneous exact subtraction and less-than comparison on actual inputs.
The result word contains the difference modulo the common bit width, and the
final borrow register is exactly the strict-comparison result. -/
theorem binary_subtraction_machine (m n : ℕ) :
    ∃ steps, let initial := loopState m.bits n.bits { carry := false } []
      (advance steps initial).phase = .halt ∧
      ((advance steps initial).regs.carry = true ↔ m < n) ∧
      (n ≤ m → value (advance steps initial).out = m - n) ∧
      bitSteps steps initial ≤ 50 * max m.size n.size + 15 := by
  obtain ⟨steps, r, hs, heq, hb⟩ := run_subtract m.bits n.bits { carry := false } []
  simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.add_zero,
    Nat.size_eq_bits_len] at hs heq
  refine ⟨steps, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    rfl
  · rw [heq]
    change r.carry = true ↔ m < n
    rw [hb]
    simpa using subtract_borrow m.bits n.bits
  · intro h
    rw [heq]
    simpa using (subtract_of_le m.bits n.bits (by simpa using h)).2
  · have hc := bitSteps_le steps (loopState m.bits n.bits { carry := false } [])
    omega

end IdentityTesting.BinarySubtractorMachine
