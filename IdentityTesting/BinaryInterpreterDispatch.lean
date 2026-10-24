import IdentityTesting.BinaryInterpreterDispatchState

namespace IdentityTesting.BinaryInterpreterDispatch
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic

def decodeOp : Bool → Bool → Bool → Option RationalOp
  | false,false,false => some .copy
  | true,false,false => some .add
  | false,true,false => some .sub
  | true,true,false => some .mul
  | false,false,true => some .div
  | true,false,true => some .le
  | _,_,_ => none

def tagView (s : State) : BinaryCodeTagDecoder.State :=
  ⟨s.tagPhase,s.io.code,s.io.history,s.first,s.second,s.third⟩
def setTag (s : State) (t : BinaryCodeTagDecoder.State) : State :=
  {s with
    tagPhase := t.phase,first := t.first,second := t.second,third := t.third,
    io := {s.io with code := t.code,history := t.history}}

/-- Choosing one of six groups changes finite control, preserving every pool
stack through rearm. No core is copied or allocated by selection. -/
def select (s : State) (op : RationalOp) : State :=
  {s with phase := .address,selected := op,pool := BinaryInterpreterPool.rearm s.pool op}

def addressView (s : State) : BinaryCodeWordLoader.State :=
  ⟨s.io.fieldPhase,s.io.code,s.io.history,s.io.temp,s.io.destination⟩
def setAddress (s : State) (a : BinaryCodeWordLoader.State) : State :=
  {s with io := {s.io with
    fieldPhase := a.phase,code := a.code,history := a.history,
    temp := a.temp,destination := a.out}}
def enterExecution (s : State) : State :=
  {s with phase := .running,io := {s.io with fieldPhase := .reading}}

def step (s : State) : State :=
  match s.phase with
  | .tag => if s.tagPhase = .halt then
      match decodeOp s.first s.second s.third with
      | some op => select s op
      | none => {s with phase := .invalid}
    else setTag s (BinaryCodeTagDecoder.step (tagView s))
  | .address => if s.io.fieldPhase = .halt then enterExecution s
      else setAddress s (BinaryCodeWordLoader.step (addressView s))
  | .running => setExec s s.selected
      (BinaryInterpreterOperandExecute.step (arithmeticStorage s.selected) (execView s s.selected))
  | .invalid => s

def transitionTrace (s : State) : List BinaryArithmetic.BitOp :=
  match s.phase with
  | .tag => if s.tagPhase = .halt then [.branch]
      else .branch :: BinaryCodeTagDecoder.transitionTrace (tagView s)
  | .address => if s.io.fieldPhase = .halt then [.branch]
      else .branch :: BinaryCodeWordLoader.transitionTrace (addressView s)
  | .running => BinaryInterpreterOperandExecute.transitionTrace (arithmeticStorage s.selected) (execView s s.selected)
  | .invalid => []

def advance : ℕ → State → State
  | 0,s => s
  | n+1,s => advance n (step s)
def bitSteps : ℕ → State → ℕ
  | 0,_ => 0
  | n+1,s => (transitionTrace s).length + bitSteps n (step s)

/-- The running label contains an absorbing halted submachine. -/
def Done (s : State) : Prop := s.phase = .running ∧ s.io.loading = false ∧ s.io.executionPhase = .halt

theorem advance_add (m n : ℕ) (s : State) : advance (m+n) s = advance n (advance m s) := by
  induction m generalizing s with
  | zero => simp [advance]
  | succ m ih => simpa [Nat.succ_add,advance] using ih (step s)
theorem bitSteps_add (m n : ℕ) (s : State) : bitSteps (m+n) s = bitSteps m s + bitSteps n (advance m s) := by
  induction m generalizing s with
  | zero => simp [bitSteps,advance]
  | succ m ih => simp [Nat.succ_add,advance,bitSteps,ih,Nat.add_assoc]

theorem done_step (s : State) (h : Done s) : step s = s := by
  rcases h with ⟨hp,hl,he⟩
  simp only [step,hp]
  have hs : BinaryInterpreterOperandExecute.step (arithmeticStorage s.selected) (execView s s.selected) =
      execView s s.selected := by
    simp [BinaryInterpreterOperandExecute.step,execView,IO.view,hl,he,BinaryInterpreterArithmeticClean.step]
  rw [hs,setExec_view]

end IdentityTesting.BinaryInterpreterDispatch
