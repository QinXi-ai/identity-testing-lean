import IdentityTesting.BinarySubtractorMachine
import IdentityTesting.BinaryWordNormalization

/-! A fixed fourteen-stack long-division machine. The initial reversal,
denominator and remainder copies, discarded words, difference transfers, and
final canonical normalizations all have explicit per-bit transitions. This
module defines the machine; its simulation and complexity bounds are separate. -/
namespace IdentityTesting.BinaryDivisionMachine
open BinaryArithmetic

inductive Phase where
  | init | scan | dToTmp | tmpToD | rToTmp | tmpToR | startSub | subtracting
  | decide | clearDiff | clearRem | diffToTmp | tmpToRem | normQ | normR | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  source : List Bool
  bits : List Bool
  divisor : List Bool
  temp : List Bool
  sub : BinarySubtractorMachine.State
  quot : BinaryWordNormalization.State
  rem : BinaryWordNormalization.State
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .init =>
      match s.source with
      | [] => { s with phase := .scan }
      | b :: bs => { s with source := bs, bits := b :: s.bits }
  | .scan =>
      match s.bits with
      | [] => { s with phase := .normQ }
      | b :: bs => { s with phase := .dToTmp, bits := bs, rem := { s.rem with source := b :: s.rem.source } }
  | .dToTmp =>
      match s.divisor with
      | [] => { s with phase := .tmpToD }
      | b :: bs => { s with divisor := bs, temp := b :: s.temp }
  | .tmpToD =>
      match s.temp with
      | [] => { s with phase := .rToTmp }
      | b :: bs => { s with temp := bs, divisor := b :: s.divisor, sub := { s.sub with right := b :: s.sub.right } }
  | .rToTmp =>
      match s.rem.source with
      | [] => { s with phase := .tmpToR }
      | b :: bs => { s with temp := b :: s.temp, rem := { s.rem with source := bs } }
  | .tmpToR =>
      match s.temp with
      | [] => { s with phase := .startSub }
      | b :: bs => { s with temp := bs, rem := { s.rem with source := b :: s.rem.source }, sub := { s.sub with left := b :: s.sub.left } }
  | .startSub => { s with phase := .subtracting, sub := { s.sub with phase := .check, regs := { carry := false } } }
  | .subtracting => if s.sub.phase = .halt then { s with phase := .decide }
      else { s with sub := BinarySubtractorMachine.step s.sub }
  | .decide => if s.sub.regs.carry then
      { s with phase := .clearDiff, quot := { s.quot with source := false :: s.quot.source } }
      else { s with phase := .clearRem, quot := { s.quot with source := true :: s.quot.source } }
  | .clearDiff =>
      match s.sub.out with
      | [] => { s with phase := .scan }
      | _ :: bs => { s with sub := { s.sub with out := bs } }
  | .clearRem =>
      match s.rem.source with
      | [] => { s with phase := .diffToTmp }
      | _ :: bs => { s with rem := { s.rem with source := bs } }
  | .diffToTmp =>
      match s.sub.out with
      | [] => { s with phase := .tmpToRem }
      | b :: bs => { s with temp := b :: s.temp, sub := { s.sub with out := bs } }
  | .tmpToRem =>
      match s.temp with
      | [] => { s with phase := .scan }
      | b :: bs => { s with temp := bs, rem := { s.rem with source := b :: s.rem.source } }
  | .normQ => if s.quot.phase = .halt then { s with phase := .normR }
      else { s with quot := BinaryWordNormalization.step s.quot }
  | .normR => if s.rem.phase = .halt then { s with phase := .halt }
      else { s with rem := BinaryWordNormalization.step s.rem }
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

def word (xs : List Bool) : BinaryWordNormalization.State := ⟨.collect, xs, [], []⟩

def ready (bits d q r : List Bool) (regs : BinarySubtractorMachine.Registers) : State :=
  ⟨.scan, [], bits, d, [], BinarySubtractorMachine.haltState regs [], word q, word r⟩

def initial (xs d : List Bool) : State :=
  ⟨.init, xs, [], d, [], BinarySubtractorMachine.haltState { carry := false } [], word [], word []⟩

/-- All transfer loops are bounded-cell operations. A two-destination copy
costs seven actions; subroutine dispatch counts its control branch too. -/
def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .init =>
      match s.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .scan =>
      match s.bits with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .dToTmp =>
      match s.divisor with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToD | .tmpToR =>
      match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .rToTmp =>
      match s.rem.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .startSub => [.branch]
  | .subtracting => if s.sub.phase = .halt then [.branch]
      else .branch :: BinarySubtractorMachine.transitionTrace s.sub
  | .decide => [.branch, .writeCell, .moveHead]
  | .clearDiff =>
      match s.sub.out with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead]
  | .clearRem =>
      match s.rem.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead]
  | .diffToTmp =>
      match s.sub.out with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToRem =>
      match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .normQ => if s.quot.phase = .halt then [.branch]
      else .branch :: BinaryWordNormalization.transitionTrace s.quot
  | .normR => if s.rem.phase = .halt then [.branch]
      else .branch :: BinaryWordNormalization.transitionTrace s.rem
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 7 := by
  have ha := BinarySubtractorMachine.transition_length s.sub
  have hq := BinaryWordNormalization.transition_length s.quot
  have hr := BinaryWordNormalization.transition_length s.rem
  cases hp : s.phase <;> simp only [transitionTrace, hp] <;>
    first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7 * n := by
  induction n generalizing s with
  | zero => simp [bitSteps]
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryDivisionMachine
