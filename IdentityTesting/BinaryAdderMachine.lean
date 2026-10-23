import IdentityTesting.BinaryArithmeticCost

/-!
# A fixed finite-control, four-stack binary addition machine

Unlike an arbitrary user-supplied arithmetic cost function, `step` below only
matches/pops/pushes one Bool stack cell or evaluates one Boolean gate. It has
12 control locations and seven Boolean registers. `advance` is the actual
small-step transition iteration. `bitSteps` sums the explicit primitive actions
of those transitions. The output is proved equal to the bit-list adder, hence
to the sum of the actual binary-encoded inputs.

This is a standalone bit-stack machine model. Translation into Mathlib's TM2,
a multiplication machine, rational reduction, and the whole oracle are separate
obligations; no claim about Lean's runtime is made.
-/

namespace IdentityTesting.BinaryAdderMachine
open BinaryArithmetic

inductive Phase where
  | check | readLeft | readRight | xorP | xorS | andG | andH | orC
  | emit | carry | reverse | halt
  deriving DecidableEq, Repr

structure Registers where
  carry : Bool
  a : Bool := false
  b : Bool := false
  p : Bool := false
  sum : Bool := false
  g : Bool := false
  h : Bool := false
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  left : List Bool
  right : List Bool
  work : List Bool
  out : List Bool
  regs : Registers
  deriving DecidableEq, Repr

/-- Every branch manipulates a bounded number of Bool cells/registers. -/
def step (s : State) : State :=
  match s.phase with
  | .check =>
      match s.left, s.right with
      | [], [] => { s with phase := .carry }
      | _, _ => { s with phase := .readLeft }
  | .readLeft =>
      match s.left with
      | [] => { s with phase := .readRight, regs := { s.regs with a := false } }
      | a :: xs => { s with phase := .readRight, left := xs, regs := { s.regs with a := a } }
  | .readRight =>
      match s.right with
      | [] => { s with phase := .xorP, regs := { s.regs with b := false } }
      | b :: ys => { s with phase := .xorP, right := ys, regs := { s.regs with b := b } }
  | .xorP => { s with phase := .xorS, regs := { s.regs with p := xor s.regs.a s.regs.b } }
  | .xorS => { s with phase := .andG, regs := { s.regs with sum := xor s.regs.p s.regs.carry } }
  | .andG => { s with phase := .andH, regs := { s.regs with g := s.regs.a && s.regs.b } }
  | .andH => { s with phase := .orC, regs := { s.regs with h := s.regs.p && s.regs.carry } }
  | .orC => { s with phase := .emit, regs := { s.regs with carry := s.regs.g || s.regs.h } }
  | .emit => { s with phase := .check, work := s.regs.sum :: s.work }
  | .carry => { s with phase := .reverse, work := if s.regs.carry then true :: s.work else s.work }
  | .reverse =>
      match s.work with
      | [] => { s with phase := .halt }
      | b :: bs => { s with work := bs, out := b :: s.out }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def loopState (xs ys : List Bool) (r : Registers) (acc : List Bool) : State :=
  ⟨.check, xs, ys, acc, [], r⟩
def reverseState (r : Registers) (work out : List Bool) : State :=
  ⟨.reverse, [], [], work, out, r⟩
def haltState (r : Registers) (out : List Bool) : State :=
  ⟨.halt, [], [], [], out, r⟩

def nextRegs (r : Registers) (a b : Bool) : Registers :=
  ⟨(a && b) || ((xor a b) && r.carry), a, b, xor a b,
    xor (xor a b) r.carry, a && b, (xor a b) && r.carry⟩

@[simp] theorem nextRegs_sum (r : Registers) (a b : Bool) :
    (nextRegs r a b).sum = (fullAdder a b r.carry).value.1 := rfl
@[simp] theorem nextRegs_carry (r : Registers) (a b : Bool) :
    (nextRegs r a b).carry = (fullAdder a b r.carry).value.2 := rfl

theorem round_steps (xs ys : List Bool) (r : Registers) (acc : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    advance 9 (loopState xs ys r acc) =
      loopState xs.tail ys.tail (nextRegs r (xs.headD false) (ys.headD false))
        ((fullAdder (xs.headD false) (ys.headD false) r.carry).value.1 :: acc) := by
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
    ∃ n, n ≤ acc.length + 4 ∧
      advance n (loopState [] [] r acc) =
        haltState r (acc.reverse ++ (BinaryArithmetic.add [] [] r.carry).value) := by
  let work := if r.carry then true :: acc else acc
  refine ⟨2 + (work.length + 1), ?_, ?_⟩
  · cases hc : r.carry <;> simp [work, hc] <;> omega
  · rw [advance_add]
    have h : advance 2 (loopState [] [] r acc) = reverseState r work [] := rfl
    rw [h, reverse_steps]
    cases hc : r.carry <;> simp [work, hc, BinaryArithmetic.add, List.reverse_cons,
      List.append_assoc]

/-- Actual small-step execution, with a bound rather than a supplied cost premise. -/
theorem run_add (xs ys : List Bool) (r : Registers) (acc : List Bool) :
    ∃ n r', n ≤ 10 * max xs.length ys.length + acc.length + 4 ∧
      advance n (loopState xs ys r acc) =
        haltState r' (acc.reverse ++ (BinaryArithmetic.add xs ys r.carry).value) := by
  by_cases he : xs = [] ∧ ys = []
  · rcases he with ⟨rfl, rfl⟩
    obtain ⟨n, hn, heq⟩ := finish_steps r acc
    exact ⟨n, r, by simpa using hn, heq⟩
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    let fa := fullAdder (xs.headD false) (ys.headD false) r.carry
    let rnext := nextRegs r (xs.headD false) (ys.headD false)
    obtain ⟨n, r', hn, heq⟩ := run_add xs.tail ys.tail rnext (fa.value.1 :: acc)
    have hlen : max xs.length ys.length = max xs.tail.length ys.tail.length + 1 := by
      cases xs <;> cases ys <;> simp_all <;> omega
    refine ⟨9 + n, r', ?_, ?_⟩
    · simp only [List.length_cons] at hn
      omega
    · rw [advance_add, round_steps xs ys r acc hne]
      change advance n (loopState xs.tail ys.tail rnext (fa.value.1 :: acc)) = _
      rw [heq, add_step_value xs ys r.carry hne]
      simp [rnext, fa, List.reverse_cons, List.append_assoc]
termination_by xs.length + ys.length
decreasing_by
  cases xs <;> cases ys <;> simp_all <;> omega

/-- The literal primitive actions performed by a transition. Stack reads include
an emptiness branch; a pop moves one head, and a push writes one bit and moves.
The reverse phase transfers one bit between two stacks in five actions. -/
def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .check => [.readCell, .readCell, .branch]
  | .readLeft =>
      match s.left with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead]
  | .readRight =>
      match s.right with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead]
  | .xorP | .xorS => [.xorGate]
  | .andG | .andH => [.andGate]
  | .orC => [.orGate]
  | .emit => [.writeCell, .moveHead]
  | .carry => if s.regs.carry then [.branch, .writeCell, .moveHead] else [.branch]
  | .reverse =>
      match s.work with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 5 := by
  cases hp : s.phase <;> simp [transitionTrace, hp] <;>
    first | split <;> simp | trivial

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 5 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

/-- A finite-state four-stack machine adds the supplied canonical binary inputs
in at most `50 * max(size m,size n) + 20` primitive bit actions. -/
theorem binary_addition_machine (m n : ℕ) :
    ∃ steps r, let initial := loopState m.bits n.bits { carry := false } []
      (advance steps initial).phase = .halt ∧
      value (advance steps initial).out = m + n ∧
      advance steps initial = haltState r (BinaryArithmetic.add m.bits n.bits false).value ∧
      bitSteps steps initial ≤ 50 * max m.size n.size + 20 := by
  obtain ⟨steps, r, hs, heq⟩ := run_add m.bits n.bits { carry := false } []
  refine ⟨steps, r, ?_⟩
  simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.add_zero,
    Nat.size_eq_bits_len] at hs heq
  dsimp only
  refine ⟨?_, ?_, heq, ?_⟩
  · rw [heq]
    rfl
  · rw [heq]
    exact (add_binary_inputs m n).1
  · have hb := bitSteps_le steps (loopState m.bits n.bits { carry := false } [])
    omega

end IdentityTesting.BinaryAdderMachine
