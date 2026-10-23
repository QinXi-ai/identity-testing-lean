import IdentityTesting.BinarySignedComparison
import IdentityTesting.BinarySubtractorMachine

/-! Signed magnitude addition. The comparator consumes explicit copies. The
original operands are then transported bit by bit into the addition/subtraction
workspace, in the order chosen by the finite comparator result. -/
namespace IdentityTesting.BinarySignedAdder
open BinaryArithmetic BinarySignedWords

inductive Phase where
  | leftCollect | leftCopy | rightCollect | rightCopy | comparing
  | leftRouteCollect | leftRouteEmit | rightRouteCollect | rightRouteEmit
  | arithmetic | outCollect | outEmit | normalizing | finish | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  negativeLeft : Bool
  negativeRight : Bool
  negative : Bool
  swap : Bool
  left : List Bool
  right : List Bool
  temp : List Bool
  compare : BinarySignedComparison.State
  arith : BinaryAdderMachine.State
  norm : BinaryWordNormalization.State
  deriving DecidableEq, Repr

def step (s : State) : State :=
  match s.phase with
  | .leftCollect => match s.left with
      | [] => { s with phase := .leftCopy }
      | b :: bs => { s with left := bs, temp := b :: s.temp }
  | .leftCopy => match s.temp with
      | [] => { s with phase := .rightCollect }
      | b :: bs => { s with temp := bs, left := b :: s.left, compare := { s.compare with left := b :: s.compare.left } }
  | .rightCollect => match s.right with
      | [] => { s with phase := .rightCopy }
      | b :: bs => { s with right := bs, temp := b :: s.temp }
  | .rightCopy => match s.temp with
      | [] => { s with phase := .comparing }
      | b :: bs => { s with temp := bs, right := b :: s.right, compare := { s.compare with right := b :: s.compare.right } }
  | .comparing => if s.compare.phase = .halt then
        { s with
          phase := .leftRouteCollect
          swap := s.compare.result && (xor s.negativeLeft s.negativeRight)
          negative := if s.compare.result && (xor s.negativeLeft s.negativeRight)
            then s.negativeRight else s.negativeLeft }
      else { s with compare := BinarySignedComparison.step s.compare }
  | .leftRouteCollect => match s.left with
      | [] => { s with phase := .leftRouteEmit }
      | b :: bs => { s with left := bs, temp := b :: s.temp }
  | .leftRouteEmit => match s.temp with
      | [] => { s with phase := .rightRouteCollect }
      | b :: bs => { s with temp := bs, arith := if s.swap then
          { s.arith with right := b :: s.arith.right } else { s.arith with left := b :: s.arith.left } }
  | .rightRouteCollect => match s.right with
      | [] => { s with phase := .rightRouteEmit }
      | b :: bs => { s with right := bs, temp := b :: s.temp }
  | .rightRouteEmit => match s.temp with
      | [] => { s with phase := .arithmetic }
      | b :: bs => { s with temp := bs, arith := if s.swap then
          { s.arith with left := b :: s.arith.left } else { s.arith with right := b :: s.arith.right } }
  | .arithmetic => if s.arith.phase = .halt then { s with phase := .outCollect }
      else { s with arith := if s.negativeLeft = s.negativeRight
        then BinaryAdderMachine.step s.arith else BinarySubtractorMachine.step s.arith }
  | .outCollect => match s.arith.out with
      | [] => { s with phase := .outEmit }
      | b :: bs => { s with temp := b :: s.temp, arith := { s.arith with out := bs } }
  | .outEmit => match s.temp with
      | [] => { s with phase := .normalizing }
      | b :: bs => { s with temp := bs, norm := { s.norm with source := b :: s.norm.source } }
  | .normalizing => if s.norm.phase = .halt then { s with phase := .finish }
      else { s with norm := BinaryWordNormalization.step s.norm }
  | .finish => { s with phase := .halt, negative := if s.norm.out = [] then false else s.negative }
  | .halt => s

def initial (x y : Word) : State :=
  ⟨.leftCollect, x.negative, y.negative, false, false, x.magnitude, y.magnitude, [],
    BinarySignedComparison.initial ⟨false, []⟩ ⟨false, []⟩,
    BinaryAdderMachine.loopState [] [] { carry := false } [], ⟨.collect, [], [], []⟩⟩

def output (s : State) : Word := ⟨s.negative, s.norm.out⟩

def advance : ℕ → State → State
  | 0, s => s
  | k + 1, s => advance k (step s)

def Runs (s : State) (k : ℕ) (t : State) : Prop := advance k s = t

theorem advance_add (m n : ℕ) (s : State) : advance (m + n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add, advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) : Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add, h, j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .leftCollect | .leftRouteCollect | .rightCollect | .rightRouteCollect |
    .outCollect => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .leftCopy | .rightCopy => [.readCell, .branch, .moveHead, .writeCell, .moveHead, .writeCell, .moveHead]
  | .leftRouteEmit | .rightRouteEmit => [.readCell, .branch, .moveHead, .branch, .writeCell, .moveHead]
  | .outEmit => [.readCell, .branch, .moveHead, .writeCell, .moveHead]
  | .comparing => if s.compare.phase = .halt then [.branch, .xorGate, .andGate, .branch]
      else .branch :: BinarySignedComparison.transitionTrace s.compare
  | .arithmetic => if s.arith.phase = .halt then [.branch] else
      .branch :: .xorGate :: .branch :: (if s.negativeLeft = s.negativeRight then
        BinaryAdderMachine.transitionTrace s.arith else BinarySubtractorMachine.transitionTrace s.arith)
  | .normalizing => if s.norm.phase = .halt then [.branch]
      else .branch :: BinaryWordNormalization.transitionTrace s.norm
  | .finish => [.readCell, .branch, .writeCell]
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0, _ => 0
  | n + 1, s => (transitionTrace s).length + bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 12 := by
  have ha := BinaryAdderMachine.transition_length s.arith
  have hs := BinarySubtractorMachine.transition_length s.arith
  have hn := BinaryWordNormalization.transition_length s.norm
  have hc : (BinarySignedComparison.transitionTrace s.compare).length ≤ 11 := by
    cases hp : s.compare.phase <;> simp only [BinarySignedComparison.transitionTrace, hp]
    · split <;> simp
    all_goals simp
  cases hp : s.phase <;> simp only [transitionTrace, hp] <;>
    first | (split <;> simp_all) | simp_all
  split <;> omega
  all_goals omega

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 12 * n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinarySignedAdder
