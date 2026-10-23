import IdentityTesting.BinaryRationalArithmeticBitCounter

/-! Binary length is computed by the bit counter, explicit output transport,
and an actual canonical normalizer. -/
namespace IdentityTesting.BinaryRationalArithmeticBitLength
open BinaryArithmetic

inductive Phase where
  | counting | collect | emit | normalize | halt
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : BinaryRationalArithmeticBitCounter.State
  norm : BinaryWordNormalization.State
  temp : List Bool
  deriving DecidableEq, Repr

def initial (xs : List Bool) : State :=
  ⟨.counting,BinaryRationalArithmeticBitCounter.initial xs,⟨.collect,[],[],[]⟩,[]⟩

def step (s : State) : State :=
  match s.phase with
  | .counting => if s.core.phase = .halt then {s with phase := .collect}
      else {s with core := BinaryRationalArithmeticBitCounter.step s.core}
  | .collect => match s.core.counter with
      | [] => {s with phase := .emit}
      | b::bs => {s with core := {s.core with counter := bs},temp := b::s.temp}
  | .emit => match s.temp with
      | [] => {s with phase := .normalize}
      | b::bs => {s with norm := {s.norm with source := b::s.norm.source},temp := bs}
  | .normalize => if s.norm.phase = .halt then {s with phase := .halt}
      else {s with norm := BinaryWordNormalization.step s.norm}
  | .halt => s

def output (s : State) : List Bool := s.norm.out

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)

def Runs (s : State) (n : ℕ) (t : State) : Prop := advance n s=t

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s=advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)

theorem Runs.trans {s t u : State} {m n : ℕ} (h : Runs s m t) (j : Runs t n u) :
    Runs s (m+n) u := by
  dsimp [Runs] at *
  rw [advance_add,h,j]

def transitionTrace (s : State) : List BitOp :=
  match s.phase with
  | .counting => if s.core.phase = .halt then [.branch]
      else .branch :: BinaryRationalArithmeticBitCounter.transitionTrace s.core
  | .collect => if s.core.counter = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .emit => if s.temp = [] then [.readCell,.branch]
      else [.readCell,.branch,.moveHead,.writeCell,.moveHead]
  | .normalize => if s.norm.phase = .halt then [.branch]
      else .branch :: BinaryWordNormalization.transitionTrace s.norm
  | .halt => []

def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)

theorem transition_length (s : State) : (transitionTrace s).length ≤ 7 := by
  have hc := BinaryRationalArithmeticBitCounter.transition_length s.core
  have hn := BinaryWordNormalization.transition_length s.norm
  cases hp:s.phase <;> simp only [transitionTrace,hp]
  all_goals first | (split <;> simp_all) | simp_all

theorem bitSteps_le (n : ℕ) (s : State) : bitSteps n s ≤ 7*n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have ht := transition_length s
      have hi := ih (step s)
      simp only [bitSteps]
      omega

end IdentityTesting.BinaryRationalArithmeticBitLength
