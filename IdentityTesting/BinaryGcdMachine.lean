import IdentityTesting.BinaryDivisionMachineBound
import IdentityTesting.BinaryEuclideanRounds

/-! A fifteen-stack Euclidean machine. The division machine's source and
divisor stacks hold the current pair; its remainder output is transferred back
one bit at a time. Quotient clearing and every word move are charged. -/
namespace IdentityTesting.BinaryGcdMachine
open BinaryArithmetic
inductive Phase where
  | check | dividing | clearQ | dToTmp | tmpToX | rToTmp | tmpToD | restart | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  div : BinaryDivisionMachine.State
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .check => match s.div.divisor with
      | [] => { s with phase := .halt }
      | _ :: _ => { s with phase := .dividing }
  | .dividing => if s.div.phase = .halt then { s with phase := .clearQ }
      else { s with div := BinaryDivisionMachine.step s.div }
  | .clearQ => match s.div.quot.out with
      | [] => { s with phase := .dToTmp }
      | _ :: bs => { s with div := { s.div with quot := { s.div.quot with out := bs } } }
  | .dToTmp => match s.div.divisor with
      | [] => { s with phase := .tmpToX }
      | b :: bs => { s with temp := b :: s.temp, div := { s.div with divisor := bs } }
  | .tmpToX => match s.temp with
      | [] => { s with phase := .rToTmp }
      | b :: bs => { s with temp := bs, div := { s.div with source := b :: s.div.source } }
  | .rToTmp => match s.div.rem.out with
      | [] => { s with phase := .tmpToD }
      | b :: bs => { s with temp := b :: s.temp, div := { s.div with rem := { s.div.rem with out := bs } } }
  | .tmpToD => match s.temp with
      | [] => { s with phase := .restart }
      | b :: bs => { s with temp := bs, div := { s.div with divisor := b :: s.div.divisor } }
  | .restart => { s with phase := .check, div := { s.div with phase := .init, sub := { s.div.sub with phase := .halt, regs := { carry := false } }, quot := { s.div.quot with phase := .collect }, rem := { s.div.rem with phase := .collect } } }
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

def ready (x y : List Bool) : State := ⟨.check, BinaryDivisionMachine.initial x y, []⟩
def terminal (x : List Bool) : State := ⟨.halt, BinaryDivisionMachine.initial x [], []⟩

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .check => [.readCell, .branch]
  | .dividing => if s.div.phase = .halt then [.branch] else .branch :: BinaryDivisionMachine.transitionTrace s.div
  | .clearQ => match s.div.quot.out with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead]
  | .dToTmp => match s.div.divisor with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToX | .tmpToD => match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .rToTmp => match s.div.rem.out with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .restart => [.branch]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 8 := by
  have hd := BinaryDivisionMachine.transition_length s.div
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

end IdentityTesting.BinaryGcdMachine
