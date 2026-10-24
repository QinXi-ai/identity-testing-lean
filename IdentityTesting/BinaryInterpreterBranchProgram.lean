import IdentityTesting.BinaryInterpreterBranchState

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation

def dispatchNode (s : State) : State :=
  match s.core.first,s.core.second,s.core.third with
  | false,false,false => control .returning s
  | true,false,false => {control .instruction s with core := BinaryInterpreterDispatch.rearm s.core}
  | false,true,false => enterNode {s with frames := .next::s.frames}
  | true,true,false => {control .comparing s with core := compareStart s.core}
  | _,_,_ => {s with phase := .invalid}

def afterCompare (s : State) : State :=
  if s.decision then enterNode {s with frames := .skipElse::s.frames}
  else enterSkip .skipToNode {s with frames := .close::s.frames}

def step (s : State) : State :=
  match s.phase with
  | .node => if s.core.tagPhase = .halt then dispatchNode s
      else {s with
        core := BinaryInterpreterDispatch.setTag s.core
          (BinaryCodeTagDecoder.step (BinaryInterpreterDispatch.tagView s.core))}
  | .instruction => if BinaryInterpreterDispatch.Done s.core then control .returning s
      else {s with core := BinaryInterpreterDispatch.step s.core}
  | .comparing => if s.comparePhase = .halt then afterCompare s
      else setCompare s (BinaryInterpreterBranchCompare.step (compareView s))
  | .skipToNode => if s.skipPhase = .halt then enterNode s
      else setSkip s (BinaryCodeSkip.step (skipView s))
  | .skipToClose => if s.skipPhase = .halt then enterClosing s
      else setSkip s (BinaryCodeSkip.step (skipView s))
  | .returning => match s.frames with
      | [] => control .halt s
      | .next::fs => enterNode {s with frames := .close::fs}
      | .close::fs => enterClosing {s with frames := fs}
      | .skipElse::fs => enterSkip .skipToClose {s with frames := fs}
  | .closing => if s.core.tagPhase = .halt then
      if s.core.first && s.core.second && s.core.third then control .returning s
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
  | .comparing => if s.comparePhase = .halt then [.branch,.writeCell,.moveHead]
      else .branch :: BinaryInterpreterBranchCompare.transitionTrace (compareView s)
  | .skipToNode | .skipToClose => if s.skipPhase = .halt then [.branch]
      else .branch :: BinaryCodeSkip.transitionTrace (skipView s)
  | .returning => match s.frames with
      | [] => [.readCell,.branch]
      | .next::_ => [.readCell,.branch,.writeCell]
      | .close::_ | .skipElse::_ => [.readCell,.branch,.moveHead]
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
  boundary .node (BinaryInterpreterDispatch.initial pool tape code history) []

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)
theorem bitSteps_add (m n : ℕ) (s : State) : bitSteps (m+n) s = bitSteps m s+bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [bitSteps,advance]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

end IdentityTesting.BinaryInterpreterBranchProgram
