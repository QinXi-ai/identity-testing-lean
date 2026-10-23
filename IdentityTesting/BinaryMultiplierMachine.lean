import IdentityTesting.BinaryAdderMachine

/-! Fixed-stack shift-and-add multiplication. Every word transfer below is an
explicit loop over single bits; no transition copies, reverses, or adds an
unbounded word as one operation. The embedded adder uses four more Bool stacks. -/

namespace IdentityTesting.BinaryMultiplierMachine
open BinaryArithmetic

inductive Phase where
  | scan | yToTmp | tmpToY | accToTmp | tmpToRight | startAdd | adding
  | outToTmp | tmpToAcc | shift | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  factor : List Bool
  shifted : List Bool
  temp : List Bool
  acc : List Bool
  adder : BinaryAdderMachine.State
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .scan =>
      match s.factor with
      | [] => { s with phase := .halt }
      | b :: bs => { s with factor := bs, phase := if b then .yToTmp else .shift }
  | .yToTmp =>
      match s.shifted with
      | [] => { s with phase := .tmpToY }
      | b :: bs => { s with shifted := bs, temp := b :: s.temp }
  | .tmpToY =>
      match s.temp with
      | [] => { s with phase := .accToTmp }
      | b :: bs => { s with temp := bs, shifted := b :: s.shifted, adder := { s.adder with left := b :: s.adder.left } }
  | .accToTmp =>
      match s.acc with
      | [] => { s with phase := .tmpToRight }
      | b :: bs => { s with acc := bs, temp := b :: s.temp }
  | .tmpToRight =>
      match s.temp with
      | [] => { s with phase := .startAdd }
      | b :: bs => { s with temp := bs, adder := { s.adder with right := b :: s.adder.right } }
  | .startAdd => { s with phase := .adding, adder := { s.adder with phase := .check, regs := { carry := false } } }
  | .adding => if s.adder.phase = .halt then { s with phase := .outToTmp }
      else { s with adder := BinaryAdderMachine.step s.adder }
  | .outToTmp =>
      match s.adder.out with
      | [] => { s with phase := .tmpToAcc }
      | b :: bs => { s with temp := b :: s.temp, adder := { s.adder with out := bs } }
  | .tmpToAcc =>
      match s.temp with
      | [] => { s with phase := .shift }
      | b :: bs => { s with temp := bs, acc := b :: s.acc }
  | .shift => { s with phase := .scan, shifted := false :: s.shifted }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

theorem advance_add (m n : ℕ) (s : State) :
    advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s = t

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) :
    Runs s (m + n) u := by
  dsimp [Runs] at *
  rw [advance_add, h, j]

theorem yToTmp_run (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.yToTmp, xs, ys, tmp, acc, a⟩ (ys.length + 1)
      ⟨.tmpToY, xs, [], ys.reverse ++ tmp, acc, a⟩ := by
  induction ys generalizing tmp with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1) ⟨.yToTmp, xs, bs, b :: tmp, acc, a⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToY_run (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.tmpToY, xs, ys, tmp, acc, a⟩ (tmp.length + 1)
      ⟨.accToTmp, xs, tmp.reverse ++ ys, [], acc,
        { a with left := tmp.reverse ++ a.left }⟩ := by
  induction tmp generalizing ys a with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1)
        ⟨.tmpToY, xs, b :: ys, bs, acc, { a with left := b :: a.left }⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih (b :: ys) { a with left := b :: a.left }]
      simp [List.reverse_cons, List.append_assoc]

theorem accToTmp_run (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.accToTmp, xs, ys, tmp, acc, a⟩ (acc.length + 1)
      ⟨.tmpToRight, xs, ys, acc.reverse ++ tmp, [], a⟩ := by
  induction acc generalizing tmp with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1) ⟨.accToTmp, xs, ys, b :: tmp, bs, a⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToRight_run (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.tmpToRight, xs, ys, tmp, acc, a⟩ (tmp.length + 1)
      ⟨.startAdd, xs, ys, [], acc, { a with right := tmp.reverse ++ a.right }⟩ := by
  induction tmp generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1)
        ⟨.tmpToRight, xs, ys, bs, acc, { a with right := b :: a.right }⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih { a with right := b :: a.right }]
      simp [List.reverse_cons, List.append_assoc]

theorem outToTmp_run (xs ys tmp acc out : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.outToTmp, xs, ys, tmp, acc, { a with out := out }⟩ (out.length + 1)
      ⟨.tmpToAcc, xs, ys, out.reverse ++ tmp, acc, { a with out := [] }⟩ := by
  induction out generalizing tmp with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1)
        ⟨.outToTmp, xs, ys, b :: tmp, acc, { a with out := bs }⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih (b :: tmp)]
      simp [List.reverse_cons, List.append_assoc]

theorem tmpToAcc_run (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) :
    Runs ⟨.tmpToAcc, xs, ys, tmp, acc, a⟩ (tmp.length + 1)
      ⟨.shift, xs, ys, [], tmp.reverse ++ acc, a⟩ := by
  induction tmp generalizing acc with
  | nil => rfl
  | cons b bs ih =>
      change advance (bs.length + 1 + 1) _ = _
      rw [advance]
      change advance (bs.length + 1) ⟨.tmpToAcc, xs, ys, bs, b :: acc, a⟩ = _
      rw [show advance (bs.length + 1) _ = _ from ih (b :: acc)]
      simp [List.reverse_cons, List.append_assoc]

private theorem adder_advance_halt (n : ℕ) (a : BinaryAdderMachine.State) (h : a.phase = .halt) :
    BinaryAdderMachine.advance n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [BinaryAdderMachine.advance, BinaryAdderMachine.step, h] using ih

/-- Subroutine execution stops at the first halt, without needing a supplied
exact running time. All earlier adder transitions are executed unchanged. -/
theorem forward_add (xs ys tmp acc : List Bool) (a : BinaryAdderMachine.State) (n : ℕ)
    (h : (BinaryAdderMachine.advance n a).phase = .halt) :
    ∃ k, k ≤ n + 1 ∧ Runs ⟨.adding, xs, ys, tmp, acc, a⟩ k
      ⟨.outToTmp, xs, ys, tmp, acc, BinaryAdderMachine.advance n a⟩ := by
  induction n generalizing a with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simp only [BinaryAdderMachine.advance] at h
      simp [Runs, advance, step, h, BinaryAdderMachine.advance]
  | succ n ih =>
      by_cases hh : a.phase = .halt
      · refine ⟨1, by omega, ?_⟩
        rw [adder_advance_halt (n + 1) a hh]
        simp [Runs, advance, step, hh]
      · obtain ⟨k, hk, he⟩ := ih (BinaryAdderMachine.step a) h
        refine ⟨k + 1, by omega, ?_⟩
        dsimp [Runs] at *
        rw [advance]
        simpa [step, hh, BinaryAdderMachine.advance] using he

end IdentityTesting.BinaryMultiplierMachine
