import IdentityTesting.BinaryInterpreterProgramInstruction
import IdentityTesting.BinaryInterpreterBranchCompare
import IdentityTesting.BinaryCodeSkip

namespace IdentityTesting.BinaryInterpreterBranchProgram
open BinaryRegisterMachine RationalComputation BinaryInterpreterArithmetic
abbrev DState := BinaryInterpreterDispatch.State

inductive Phase where
  | node | instruction | returning | closing | comparing | skipToNode | skipToClose | halt | invalid
  deriving DecidableEq, Repr
inductive Frame where
  | next | close | skipElse
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  core : DState
  frames : List Frame
  comparePhase : BinaryInterpreterBranchCompare.Phase
  decision : Bool
  skipPhase : BinaryCodeSkip.Phase
  tasks : List BinaryCodeSkip.Task

/-- A specification of a boundary state. Transitions below never erase a task
stack by replacing it with this constructor. -/
def boundary (phase : Phase) (core : DState) (frames : List Frame) : State :=
  ⟨phase,core,frames,.loading,false,.start,[]⟩

/-- Reset finite control only, retaining all physical stacks. -/
def control (phase : Phase) (s : State) : State :=
  {s with phase := phase,comparePhase := .loading,decision := false,skipPhase := .start}
def resetTag := BinaryInterpreterProgram.resetTag
def enterNode (s : State) : State := {control .node s with core := resetTag s.core}
def enterClosing (s : State) : State := {control .closing s with core := resetTag s.core}
def enterSkip (next : Phase) (s : State) : State :=
  {control next s with core := resetTag s.core}

def compareView (s : State) : BinaryInterpreterBranchCompare.State :=
  ⟨s.comparePhase,
    BinaryInterpreterOperandExecute.pairView (arithmeticStorage .le) (BinaryInterpreterDispatch.execView s.core .le),
    s.decision,s.core.cursor .le⟩
def setCompare (s : State) (c : BinaryInterpreterBranchCompare.State) : State :=
  let e := BinaryInterpreterOperandExecute.setPair (arithmeticStorage .le)
    (BinaryInterpreterDispatch.execView s.core .le) c.pair
  {s with
    comparePhase := c.phase
    decision := c.decision
    core := BinaryInterpreterDispatch.setExec s.core .le
      {e with execution := {e.execution with cursor := c.cursor}}}

def compareStart (core : DState) : DState :=
  {BinaryInterpreterDispatch.rearm core with pool := BinaryInterpreterPool.rearm core.pool .le}

def skipView (s : State) : BinaryCodeSkip.State :=
  ⟨s.skipPhase,s.core.io.code,s.core.io.history,s.tasks,s.core.tagPhase,
    s.core.first,s.core.second,s.core.third⟩
def setSkip (s : State) (k : BinaryCodeSkip.State) : State :=
  {s with
    skipPhase := k.phase
    tasks := k.tasks
    core := BinaryInterpreterDispatch.setTag s.core
      ⟨k.tagPhase,k.code,k.history,k.first,k.second,k.third⟩}

theorem compareView_set (s : State) (c : BinaryInterpreterBranchCompare.State) :
    compareView (setCompare s c) = c := by
  cases c
  simp only [compareView,setCompare,BinaryInterpreterDispatch.execView_set]
  simp [BinaryInterpreterOperandExecute.pairView,BinaryInterpreterOperandExecute.setPair,
    BinaryInterpreterDispatch.setExec]

theorem setCompare_set (s : State) (c d : BinaryInterpreterBranchCompare.State) :
    setCompare (setCompare s c) d = setCompare s d := by
  simp [setCompare,BinaryInterpreterDispatch.execView_set,
    BinaryInterpreterOperandExecute.setPair,BinaryInterpreterDispatch.setExec_set]

theorem setCompare_view (s : State) : setCompare s (compareView s) = s := by
  simp [setCompare,compareView,BinaryInterpreterOperandExecute.set_view,
    BinaryInterpreterDispatch.execView,BinaryInterpreterDispatch.IO.view,
    BinaryInterpreterDispatch.setExec,BinaryInterpreterDispatch.IO.ofExec,
    BinaryInterpreterPool.set_self]

theorem skipView_set (s : State) (k : BinaryCodeSkip.State) : skipView (setSkip s k) = k := by
  cases k
  rfl
theorem setSkip_set (s : State) (k l : BinaryCodeSkip.State) : setSkip (setSkip s k) l = setSkip s l := rfl
theorem setSkip_view (s : State) : setSkip s (skipView s) = s := rfl

end IdentityTesting.BinaryInterpreterBranchProgram
