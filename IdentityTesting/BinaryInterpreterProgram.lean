import IdentityTesting.BinaryInterpreterDispatchReuse

/-! The outer program controller shares the instruction machine's physical
state. Its continuation stack has a fixed two-symbol alphabet. This version
executes skip, instruction and sequence nodes; other node tags are rejected. -/
namespace IdentityTesting.BinaryInterpreterProgram
open BinaryRegisterMachine RationalComputation
abbrev DState := BinaryInterpreterDispatch.State

inductive Phase where
  | node | instruction | returning | closing | halt | invalid
  deriving DecidableEq, Repr
inductive Frame where
  | next | close
  deriving DecidableEq, Repr
structure State where
  phase : Phase
  core : DState
  frames : List Frame

instance (s : DState) : Decidable (BinaryInterpreterDispatch.Done s) :=
  inferInstanceAs (Decidable (s.phase = .running ∧ s.io.loading = false ∧ s.io.executionPhase = .halt))

def resetTag (s : DState) : DState :=
  {s with tagPhase := .first,first := false,second := false,third := false}

def dispatchNode (s : State) : State :=
  match s.core.first,s.core.second,s.core.third with
  | false,false,false => {s with phase := .returning}
  | true,false,false => {s with phase := .instruction,core := BinaryInterpreterDispatch.rearm s.core}
  | false,true,false => {s with phase := .node,core := resetTag s.core,frames := .next::s.frames}
  | _,_,_ => {s with phase := .invalid}

def step (s : State) : State :=
  match s.phase with
  | .node => if s.core.tagPhase = .halt then dispatchNode s
      else {s with
        core := BinaryInterpreterDispatch.setTag s.core
          (BinaryCodeTagDecoder.step (BinaryInterpreterDispatch.tagView s.core))}
  | .instruction => if BinaryInterpreterDispatch.Done s.core then {s with phase := .returning}
      else {s with core := BinaryInterpreterDispatch.step s.core}
  | .returning => match s.frames with
      | [] => {s with phase := .halt}
      | .next::fs => {s with phase := .node,core := resetTag s.core,frames := .close::fs}
      | .close::fs => {s with phase := .closing,core := resetTag s.core,frames := fs}
  | .closing => if s.core.tagPhase = .halt then
      if s.core.first && s.core.second && s.core.third then {s with phase := .returning}
      else {s with phase := .invalid}
    else {s with
      core := BinaryInterpreterDispatch.setTag s.core
        (BinaryCodeTagDecoder.step (BinaryInterpreterDispatch.tagView s.core))}
  | .halt | .invalid => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .node => if s.core.tagPhase = .halt then [.branch,.writeCell,.moveHead]
      else .branch :: BinaryCodeTagDecoder.transitionTrace (BinaryInterpreterDispatch.tagView s.core)
  | .instruction => if BinaryInterpreterDispatch.Done s.core then [.branch]
      else .branch :: BinaryInterpreterDispatch.transitionTrace s.core
  | .returning => match s.frames with
      | [] => [.readCell,.branch]
      | .next::_ => [.readCell,.branch,.writeCell]
      | .close::_ => [.readCell,.branch,.moveHead]
  | .closing => if s.core.tagPhase = .halt then [.branch]
      else .branch :: BinaryCodeTagDecoder.transitionTrace (BinaryInterpreterDispatch.tagView s.core)
  | .halt | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length+bitSteps n (step s)
def initial (pool : BinaryInterpreterPool.Pool) (tape code history : List Symbol) : State :=
  ⟨.node,BinaryInterpreterDispatch.initial pool tape code history,[]⟩

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)
theorem bitSteps_add (m n : ℕ) (s : State) : bitSteps (m+n) s = bitSteps m s+bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [bitSteps,advance]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

end IdentityTesting.BinaryInterpreterProgram
