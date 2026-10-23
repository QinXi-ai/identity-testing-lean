import IdentityTesting.BinaryWordNormalization

/-! A three-stack preserving copy. This is used for operand/result transport in
the arithmetic-instruction interface, so invoking an arithmetic machine never
silently duplicates an unbounded word. -/
namespace IdentityTesting.BinaryCopyMachine
open BinaryArithmetic

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
  | .collect => match s.source with
      | [] => { s with phase := .emit }
      | b :: bs => { s with source := bs, work := b :: s.work }
  | .emit => match s.work with
      | [] => { s with phase := .halt }
      | b :: bs => { s with work := bs, source := b :: s.source, out := b :: s.out }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) : advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem collect_run (xs work out : List Bool) :
    advance (xs.length + 1) ⟨.collect, xs, work, out⟩ =
      ⟨.emit, [], xs.reverse ++ work, out⟩ := by
  induction xs generalizing work with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.collect, xs, b :: work, out⟩ = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

theorem emit_run (xs source out : List Bool) :
    advance (xs.length + 1) ⟨.emit, source, xs, out⟩ =
      ⟨.halt, xs.reverse ++ source, [], xs.reverse ++ out⟩ := by
  induction xs generalizing source out with
  | nil => rfl
  | cons b xs ih =>
      change advance (xs.length + 1 + 1) _ = _
      rw [advance]
      change advance (xs.length + 1) ⟨.emit, b :: source, xs, b :: out⟩ = _
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

def initial (xs : List Bool) : State := ⟨.collect, xs, [], []⟩

theorem copy_run (xs : List Bool) : advance (2 * xs.length + 2) (initial xs) = ⟨.halt, xs, [], xs⟩ := by
  have ht : 2 * xs.length + 2 = (xs.length + 1) + (xs.reverse.length + 1) := by simp; omega
  rw [ht, advance_add]
  unfold initial
  rw [collect_run]
  simp only [List.append_nil]
  rw [emit_run]
  simp

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .collect => match s.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .emit => match s.work with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 7 := by
  cases hp : s.phase <;> simp only [transitionTrace, hp]
  · split <;> simp
  · split <;> simp
  · simp

theorem bitSteps_le (k : ℕ) (s : State) : bitSteps k s ≤ 7 * k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

def copyCost (xs : List Bool) : ℕ := bitSteps (2 * xs.length + 2) (initial xs)

theorem copyCost_le (xs : List Bool) : copyCost xs ≤ 14 * xs.length + 14 := by
  have h := bitSteps_le (2 * xs.length + 2) (initial xs)
  dsimp [copyCost]
  omega

end IdentityTesting.BinaryCopyMachine
