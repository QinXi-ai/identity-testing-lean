import IdentityTesting.BinaryGcdMachineBound

/-! A fixed 44-stack rational-normalization machine: copy the two input words
into the gcd machine, copy its result into two division machines, divide, and
clear a negative-zero sign. Every copy is an explicit per-bit loop. -/
namespace IdentityTesting.BinaryRationalNormalizationMachine
open BinaryArithmetic

inductive Phase where
  | nToTmp | tmpToN | dToTmp | tmpToD | gcd | gToTmp | tmpToG | divN | divD | sign | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  negative : Bool
  gcd : BinaryGcdMachine.State
  num : BinaryDivisionMachine.State
  den : BinaryDivisionMachine.State
  temp : List Bool
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .nToTmp => match s.num.source with
      | [] => { s with phase := .tmpToN }
      | b :: bs => { s with temp := b :: s.temp, num := { s.num with source := bs } }
  | .tmpToN => match s.temp with
      | [] => { s with phase := .dToTmp }
      | b :: bs => { s with temp := bs, num := { s.num with source := b :: s.num.source }, gcd := { s.gcd with div := { s.gcd.div with source := b :: s.gcd.div.source } } }
  | .dToTmp => match s.den.source with
      | [] => { s with phase := .tmpToD }
      | b :: bs => { s with temp := b :: s.temp, den := { s.den with source := bs } }
  | .tmpToD => match s.temp with
      | [] => { s with phase := .gcd }
      | b :: bs => { s with temp := bs, den := { s.den with source := b :: s.den.source }, gcd := { s.gcd with div := { s.gcd.div with divisor := b :: s.gcd.div.divisor } } }
  | .gcd => if s.gcd.phase = .halt then { s with phase := .gToTmp }
      else { s with gcd := BinaryGcdMachine.step s.gcd }
  | .gToTmp => match s.gcd.div.source with
      | [] => { s with phase := .tmpToG }
      | b :: bs => { s with temp := b :: s.temp, gcd := { s.gcd with div := { s.gcd.div with source := bs } } }
  | .tmpToG => match s.temp with
      | [] => { s with phase := .divN }
      | b :: bs => { s with temp := bs, num := { s.num with divisor := b :: s.num.divisor }, den := { s.den with divisor := b :: s.den.divisor } }
  | .divN => if s.num.phase = .halt then { s with phase := .divD }
      else { s with num := BinaryDivisionMachine.step s.num }
  | .divD => if s.den.phase = .halt then { s with phase := .sign }
      else { s with den := BinaryDivisionMachine.step s.den }
  | .sign => { s with phase := .halt, negative := if s.num.quot.out = [] then false else s.negative }
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

def initial (negative : Bool) (num den : List Bool) : State :=
  ⟨.nToTmp, negative, BinaryGcdMachine.ready [] [], BinaryDivisionMachine.initial num [],
    BinaryDivisionMachine.initial den [], []⟩

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .nToTmp => match s.num.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .dToTmp => match s.den.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .gToTmp => match s.gcd.div.source with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .tmpToN | .tmpToD | .tmpToG => match s.temp with
      | [] => [.readCell, .branch]
      | _ :: _ => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .gcd => if s.gcd.phase = .halt then [.branch] else .branch :: BinaryGcdMachine.transitionTrace s.gcd
  | .divN => if s.num.phase = .halt then [.branch] else .branch :: BinaryDivisionMachine.transitionTrace s.num
  | .divD => if s.den.phase = .halt then [.branch] else .branch :: BinaryDivisionMachine.transitionTrace s.den
  | .sign => [.readCell, .branch, .writeCell]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 9 := by
  have hg := BinaryGcdMachine.transition_length s.gcd
  have hn := BinaryDivisionMachine.transition_length s.num
  have hd := BinaryDivisionMachine.transition_length s.den
  cases hp : s.phase <;> simp only [transitionTrace, hp] <;>
    first | (split <;> simp_all) | simp_all
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 9 * n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryRationalNormalizationMachine
