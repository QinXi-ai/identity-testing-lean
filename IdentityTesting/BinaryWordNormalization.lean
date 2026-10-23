import IdentityTesting.BinaryArithmeticCost

/-! Canonical binary normalization by an explicit three-stack, finite-control
machine. This prevents accumulated high zero bits from invalidating repeated
division/gcd length bounds. No integer conversion is an executed instruction. -/
namespace IdentityTesting.BinaryWordNormalization
open BinaryArithmetic

def prependNormalized (b : Bool) (out : List Bool) : List Bool :=
  match out with
  | [] => if b then [true] else []
  | _ :: _ => b :: out

def trim (xs : List Bool) : List Bool := xs.foldr prependNormalized []

theorem trim_eq_bits (xs : List Bool) : trim xs = (value xs).bits := by
  induction xs with
  | nil => simp [trim, value]
  | cons b bs ih =>
      change prependNormalized b (trim bs) = (value (b :: bs)).bits
      cases b with
      | true =>
          have hp : prependNormalized true (trim bs) = true :: trim bs := by
            cases trim bs <;> rfl
          rw [hp, ih]
          simpa [value, Nat.add_comm] using (Nat.bit1_bits (value bs)).symm
      | false =>
          by_cases he : trim bs = []
          · have hv : value bs = 0 := by
              simpa [value] using congrArg value (ih.symm.trans he)
            simp [prependNormalized, he, value, hv]
          · have hv : value bs ≠ 0 := by
              intro hv
              apply he
              rw [ih, hv, Nat.zero_bits]
            have hp : prependNormalized false (trim bs) = false :: trim bs := by
              cases hh : trim bs with
              | nil => exact (he hh).elim
              | cons b bs => rfl
            rw [hp, ih]
            simpa [value] using (Nat.bit0_bits (value bs) hv).symm

@[simp] theorem trim_value (xs : List Bool) : value (trim xs) = value xs := by
  rw [trim_eq_bits, value_bits]

@[simp] theorem trim_length (xs : List Bool) : (trim xs).length = (value xs).size := by
  rw [trim_eq_bits, Nat.size_eq_bits_len]

def emitWord : List Bool → List Bool → List Bool
  | [], out => out
  | b :: bs, out => emitWord bs (prependNormalized b out)

theorem emitWord_append (xs ys out : List Bool) :
    emitWord (xs ++ ys) out = emitWord ys (emitWord xs out) := by
  induction xs generalizing out with
  | nil => rfl
  | cons b bs ih => exact ih (prependNormalized b out)

theorem emitWord_reverse (xs out : List Bool) :
    emitWord xs.reverse out = xs.foldr prependNormalized out := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, emitWord_append]
      simp [emitWord, ih]

inductive Phase where
  | collect | emit | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  source : List Bool
  work : List Bool
  out : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .collect =>
      match s.source with
      | [] => { s with phase := .emit }
      | b :: bs => { s with source := bs, work := b :: s.work }
  | .emit =>
      match s.work with
      | [] => { s with phase := .halt }
      | b :: bs => { s with work := bs, out := prependNormalized b s.out }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem collect_run (xs work out : List Bool) :
    advance (xs.length + 1) ⟨.collect, xs, work, out⟩ =
      ⟨.emit, [], xs.reverse ++ work, out⟩ := by
  induction xs generalizing work with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1) ⟨.collect, bs, b :: work, out⟩ = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem emit_run (work out : List Bool) :
    advance (work.length + 1) ⟨.emit, [], work, out⟩ =
      ⟨.halt, [], [], emitWord work out⟩ := by
  induction work generalizing out with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      exact ih (prependNormalized b out)

theorem normalization_run (xs : List Bool) :
    advance (2 * xs.length + 2) ⟨.collect, xs, [], []⟩ = ⟨.halt, [], [], trim xs⟩ := by
  have hn : 2 * xs.length + 2 = (xs.length + 1) + (xs.reverse.length + 1) := by simp; omega
  rw [hn, advance_add, collect_run]
  simp only [List.append_nil]
  rw [emit_run, emitWord_reverse]
  rfl

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .collect =>
      match s.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .emit =>
      match s.work with
      | [] => [.readCell, .branch]
      | b :: _ =>
          if s.out = [] ∧ b = false then [.readCell, .branch, .moveHead, .branch]
          else [.readCell, .branch, .moveHead, .branch, .writeCell, .moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 6 := by
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  · split <;> simp
  · split
    · simp
    · split <;> simp
  · simp

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 6 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

theorem binary_normalization_machine (xs : List Bool) :
    let initial : State := ⟨.collect, xs, [], []⟩
    let final := advance (2 * xs.length + 2) initial
    final.phase = .halt ∧ final.out = (value xs).bits ∧
      value final.out = value xs ∧ final.out.length = (value xs).size ∧
      bitSteps (2 * xs.length + 2) initial ≤ 12 * xs.length + 12 := by
  dsimp only
  rw [normalization_run]
  refine ⟨rfl, trim_eq_bits xs, trim_value xs, trim_length xs, ?_⟩
  have h := bitSteps_le (2 * xs.length + 2) ⟨.collect, xs, [], []⟩
  omega

end IdentityTesting.BinaryWordNormalization
