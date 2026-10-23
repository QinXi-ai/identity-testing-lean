import IdentityTesting.BinarySignedWords
import IdentityTesting.BinaryMultiplierBound

namespace IdentityTesting.BinarySignedMultiplier
open BinaryArithmetic BinarySignedWords

inductive Phase where
  | start | multiplying | outToTmp | tmpToNorm | normalizing | finish | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  signLeft : Bool
  signRight : Bool
  negative : Bool
  mul : BinaryMultiplierMachine.State
  norm : BinaryWordNormalization.State
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .start => { s with phase := .multiplying, negative := xor s.signLeft s.signRight }
  | .multiplying => if s.mul.phase = .halt then { s with phase := .outToTmp }
      else { s with mul := BinaryMultiplierMachine.step s.mul }
  | .outToTmp => match s.mul.acc with
      | [] => { s with phase := .tmpToNorm }
      | b :: bs => { s with temp := b :: s.temp, mul := { s.mul with acc := bs } }
  | .tmpToNorm => match s.temp with
      | [] => { s with phase := .normalizing }
      | b :: bs => { s with temp := bs, norm := { s.norm with source := b :: s.norm.source } }
  | .normalizing => if s.norm.phase = .halt then { s with phase := .finish }
      else { s with norm := BinaryWordNormalization.step s.norm }
  | .finish => { s with phase := .halt, negative := if s.norm.out = [] then false else s.negative }
  | .halt => s

def advance : ℕ → State → State
  | 0, s => s
  | n + 1, s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s = t

theorem advance_add (m n : ℕ) (s : State) : advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m + n) u := by
  dsimp [Runs] at *
  rw [advance_add, h, j]

def initial (a b : Bool) (xs ys : List Bool) : State :=
  ⟨.start, a, b, false, BinaryMultiplierMachine.ready xs ys [] { carry := false },
    ⟨.collect, [], [], []⟩, []⟩

def output (s : State) : Word := ⟨s.negative, s.norm.out⟩

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .start => [.xorGate]
  | .multiplying => if s.mul.phase = .halt then [.branch] else .branch :: BinaryMultiplierMachine.transitionTrace s.mul
  | .outToTmp => match s.mul.acc with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToNorm => match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .normalizing => if s.norm.phase = .halt then [.branch] else .branch :: BinaryWordNormalization.transitionTrace s.norm
  | .finish => [.readCell, .branch, .writeCell]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 8 := by
  have hm := BinaryMultiplierMachine.transition_length s.mul
  have hn := BinaryWordNormalization.transition_length s.norm
  cases hp : s.phase <;> simp only [transitionTrace, hp] <;>
    first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 8 * n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinarySignedMultiplier
